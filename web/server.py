from __future__ import annotations

import json
import mimetypes
import os
import shutil
import subprocess
import sys
import threading
import time
import traceback
import uuid
from http import HTTPStatus
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import unquote, urlparse

from web.formula_parser import parse_formula

ROOT = Path(__file__).resolve().parents[1]
STATIC_DIR = Path(__file__).resolve().parent / "static"
RUNS_DIR = Path(__file__).resolve().parent / "runs"
RUNS_DIR.mkdir(parents=True, exist_ok=True)

PROOF_TIMEOUT_SECONDS = max(1, int(os.environ.get("LABIKS_PROOF_TIMEOUT", "1800")))
LATEX_TIMEOUT_SECONDS = max(1, int(os.environ.get("LABIKS_LATEX_TIMEOUT", "40")))
RUN_TTL_SECONDS = max(60, int(os.environ.get("LABIKS_RUN_TTL", "3600")))
MAX_CONCURRENT_PROOFS = max(1, int(os.environ.get("LABIKS_MAX_CONCURRENT", "2")))

PROOF_SLOTS = threading.BoundedSemaphore(MAX_CONCURRENT_PROOFS)
ACTIVE_RUNS: set[str] = set()
ACTIVE_RUNS_LOCK = threading.Lock()


class ProverTimeoutError(RuntimeError):
    pass


class ProverBusyError(RuntimeError):
    pass


def cleanup_expired_runs(max_age_seconds: int = RUN_TTL_SECONDS) -> None:
    """Delete inactive run directories older than the configured retention period."""
    cutoff = time.time() - max_age_seconds
    with ACTIVE_RUNS_LOCK:
        active = set(ACTIVE_RUNS)

    for child in RUNS_DIR.iterdir():
        if child.name.startswith("."):
            continue
        if child.name in active:
            continue
        try:
            if child.stat().st_mtime >= cutoff:
                continue
            if child.is_dir():
                shutil.rmtree(child)
            else:
                child.unlink()
        except FileNotFoundError:
            pass
        except OSError as exc:
            print(f"[web] Could not clean {child}: {exc}")


def remove_latex_auxiliary_files(run_dir: Path) -> None:
    for pattern in (
        "*.aux",
        "*.log",
        "*.out",
        "*.toc",
        "*.fls",
        "*.fdb_latexmk",
        "*.synctex.gz",
    ):
        for path in run_dir.glob(pattern):
            try:
                path.unlink()
            except FileNotFoundError:
                pass



def compile_tex(tex_path: Path) -> tuple[bool, str | None]:
    if shutil.which("pdflatex") is None:
        return False, "Install pdflatex to compile the generated TeX file."

    try:
        proc = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", tex_path.name],
            cwd=tex_path.parent,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=LATEX_TIMEOUT_SECONDS,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return False, f"LaTeX compilation exceeded {LATEX_TIMEOUT_SECONDS} seconds."

    pdf_path = tex_path.with_suffix(".pdf")
    if proc.returncode == 0 and pdf_path.is_file():
        return True, None

    diagnostic = ""
    if proc.stdout:
        lines = [line.strip() for line in proc.stdout.splitlines() if line.strip()]
        diagnostic = lines[-1] if lines else ""
    message = "LaTeX could not compile the generated file."
    if diagnostic:
        message += f" Last message: {diagnostic[:240]}"
    return False, message


def compile_requested_tex(run_dir: Path, compile_all: bool, provable: bool) -> tuple[list[str], str | None]:
    generated: list[str] = []
    countermodel_error: str | None = None

    countermodel_tex = run_dir / "countermodel.tex"

    targets: list[Path] = []
    if compile_all:
        targets.extend(sorted(run_dir.glob("*.tex")))
    elif not provable and countermodel_tex.exists():
        targets.append(countermodel_tex)

    seen: set[Path] = set()
    for tex_path in targets:
        if tex_path in seen:
            continue
        seen.add(tex_path)
        ok, error = compile_tex(tex_path)
        if ok:
            generated.append(tex_path.with_suffix(".pdf").name)
        elif tex_path.name == "countermodel.tex":
            countermodel_error = error

    if not provable:
        if not countermodel_tex.exists():
            countermodel_error = "The prover did not generate countermodel.tex."
        elif shutil.which("pdflatex") is None:
            countermodel_error = "Install pdflatex to preview the generated countermodel."
        elif not (run_dir / "countermodel.pdf").exists() and countermodel_error is None:
            countermodel_error = "countermodel.tex was generated, but LaTeX could not compile it."

    return generated, countermodel_error


def execute_prover_worker(formula_source: str, run_dir: Path) -> dict:
    input_path = run_dir / ".request.json"
    result_path = run_dir / ".result.json"
    input_path.write_text(json.dumps({"formula": formula_source}, ensure_ascii=False), encoding="utf-8")

    command = [
        sys.executable,
        "-m",
        "web.worker",
        str(input_path),
        str(result_path),
        str(run_dir),
    ]
    try:
        proc = subprocess.run(
            command,
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=PROOF_TIMEOUT_SECONDS,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise ProverTimeoutError(
            f"Proof search exceeded {PROOF_TIMEOUT_SECONDS} seconds. Try a smaller formula."
        ) from exc
    finally:
        try:
            input_path.unlink()
        except FileNotFoundError:
            pass

    if not result_path.is_file():
        detail = (proc.stderr or proc.stdout or "").strip()
        raise RuntimeError(f"The prover worker stopped without a result. {detail[:300]}")

    try:
        result = json.loads(result_path.read_text(encoding="utf-8"))
    finally:
        try:
            result_path.unlink()
        except FileNotFoundError:
            pass

    if not result.get("ok"):
        if result.get("traceback"):
            print(result["traceback"])
        raise RuntimeError(result.get("error", "The prover worker failed."))
    return result


def run_prover(formula_source: str, compile_pdf: bool) -> dict:
    # Validate before allocating a run directory or starting another process.
    parse_formula(formula_source)
    cleanup_expired_runs()

    if not PROOF_SLOTS.acquire(timeout=1):
        raise ProverBusyError("The prover is busy. Please try again in a moment.")

    run_id = uuid.uuid4().hex
    run_dir = RUNS_DIR / run_id
    run_dir.mkdir(parents=True, exist_ok=False)
    with ACTIVE_RUNS_LOCK:
        ACTIVE_RUNS.add(run_id)

    try:
        worker_result = execute_prover_worker(formula_source, run_dir)
        provable = bool(worker_result["provable"])
        pdfs, countermodel_pdf_error = compile_requested_tex(run_dir, compile_pdf, provable)
        remove_latex_auxiliary_files(run_dir)

        countermodel_pdf = run_dir / "countermodel.pdf"
        countermodel_pdf_url = (
            f"/runs/{run_id}/countermodel.pdf" if countermodel_pdf.is_file() else None
        )

        pdfs = sorted(set(pdfs), key=lambda name: (name != "countermodel.pdf", name))
        tex_files = sorted(path.name for path in run_dir.glob("*.tex"))
        artifacts = [
            {
                "name": name,
                "kind": Path(name).suffix.lstrip("."),
                "url": f"/runs/{run_id}/{name}",
            }
            for name in [*pdfs, *tex_files]
        ]

        return {
            "ok": True,
            "run_id": run_id,
            "formula": worker_result["formula"],
            "provable": provable,
            "output": worker_result.get("output", ""),
            "artifacts": artifacts,
            "pdf_available": shutil.which("pdflatex") is not None,
            "countermodel_pdf_url": countermodel_pdf_url,
            "countermodel_pdf_error": countermodel_pdf_error,
        }
    except Exception:
        # Keep generated TeX on ordinary LaTeX errors, but remove empty/failed worker runs.
        if not any(run_dir.glob("*.tex")):
            shutil.rmtree(run_dir, ignore_errors=True)
        raise
    finally:
        with ACTIVE_RUNS_LOCK:
            ACTIVE_RUNS.discard(run_id)
        PROOF_SLOTS.release()


class Handler(SimpleHTTPRequestHandler):
    server_version = "labIKsLocal/2.0"

    def log_message(self, fmt: str, *args):
        print(f"[web] {self.address_string()} - {fmt % args}")

    def send_json(self, payload: dict, status: int = 200):
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.wfile.write(data)

    def do_POST(self):
        if urlparse(self.path).path != "/api/prove":
            self.send_error(HTTPStatus.NOT_FOUND)
            return
        try:
            length = int(self.headers.get("Content-Length", "0"))
            if length <= 0 or length > 20_000:
                raise ValueError("Invalid request size.")
            body = json.loads(self.rfile.read(length).decode("utf-8"))
            result = run_prover(body.get("formula", ""), bool(body.get("compile_pdf", False)))
            self.send_json(result)
        except (ValueError, json.JSONDecodeError) as exc:
            self.send_json({"ok": False, "error": str(exc)}, 400)
        except ProverBusyError as exc:
            self.send_json({"ok": False, "error": str(exc)}, 503)
        except ProverTimeoutError as exc:
            self.send_json({"ok": False, "error": str(exc)}, 408)
        except Exception as exc:
            traceback.print_exc()
            self.send_json({"ok": False, "error": f"Prover failed: {exc}"}, 500)

    def do_GET(self):
        path = unquote(urlparse(self.path).path)
        if path == "/":
            return self.serve_file(STATIC_DIR / "index.html")
        if path.startswith("/static/"):
            return self.serve_safe(STATIC_DIR, Path(path.removeprefix("/static/")))
        if path.startswith("/runs/"):
            return self.serve_safe(RUNS_DIR, Path(path.removeprefix("/runs/")), inline=True)
        if path == "/api/health":
            return self.send_json(
                {
                    "ok": True,
                    "pdf_available": shutil.which("pdflatex") is not None,
                    "proof_timeout_seconds": PROOF_TIMEOUT_SECONDS,
                    "run_ttl_seconds": RUN_TTL_SECONDS,
                }
            )
        self.send_error(HTTPStatus.NOT_FOUND)

    def serve_safe(self, base: Path, rel: Path, inline: bool = False):
        target = (base / rel).resolve()
        try:
            target.relative_to(base.resolve())
        except ValueError:
            self.send_error(HTTPStatus.FORBIDDEN)
            return
        self.serve_file(target, inline=inline)

    def serve_file(self, path: Path, inline: bool = False):
        if not path.is_file():
            self.send_error(HTTPStatus.NOT_FOUND)
            return
        data = path.read_bytes()
        content_type = mimetypes.guess_type(path.name)[0] or "application/octet-stream"
        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("X-Content-Type-Options", "nosniff")
        if path.is_relative_to(RUNS_DIR):
            self.send_header("Cache-Control", "no-store")
        if inline:
            safe_name = path.name.replace('"', "")
            self.send_header("Content-Disposition", f'inline; filename="{safe_name}"')
        self.end_headers()
        self.wfile.write(data)


def main():
    cleanup_expired_runs()
    host = os.environ.get("LABIKS_HOST", "127.0.0.1")
    port = int(os.environ.get("PORT", os.environ.get("LABIKS_PORT", "8000")))
    server = ThreadingHTTPServer((host, port), Handler)
    print(f"labIKs web is running at http://{host}:{port}")
    print("Press Ctrl+C to stop.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
