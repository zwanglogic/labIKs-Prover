from __future__ import annotations

import ast
import contextlib
import io
import json
import mimetypes
import os
import shutil
import subprocess
import sys
import threading
import traceback
import uuid
from http import HTTPStatus
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import unquote, urlparse

ROOT = Path(__file__).resolve().parents[1]
PROVER_DIR = ROOT / "prover"
STATIC_DIR = Path(__file__).resolve().parent / "static"
RUNS_DIR = Path(__file__).resolve().parent / "runs"
RUNS_DIR.mkdir(exist_ok=True)


def clear_runs(except_run_id: str | None = None) -> None:
    """Remove generated run directories, optionally preserving one active run."""
    for child in RUNS_DIR.iterdir():
        if except_run_id and child.name == except_run_id:
            continue
        try:
            if child.is_dir():
                shutil.rmtree(child)
            else:
                child.unlink()
        except FileNotFoundError:
            pass


def remove_latex_auxiliary_files(run_dir: Path) -> None:
    """Keep user-facing TeX/PDF files and discard LaTeX build debris."""
    for pattern in ("*.aux", "*.log", "*.out", "*.toc", "*.fls", "*.fdb_latexmk", "*.synctex.gz"):
        for path in run_dir.glob(pattern):
            try:
                path.unlink()
            except FileNotFoundError:
                pass

sys.path.insert(0, str(PROVER_DIR))
from syntax import And, Bot, Box, Diamond, Imp, Or, Prop  # noqa: E402
from search import proof_search_visual  # noqa: E402

CONSTRUCTORS = {
    "Prop": Prop,
    "Bot": Bot,
    "And": And,
    "Or": Or,
    "Imp": Imp,
    "Box": Box,
    "Diamond": Diamond,
}
ARITY = {"Prop": 1, "Bot": 0, "And": 2, "Or": 2, "Imp": 2, "Box": 1, "Diamond": 1}
PROOF_LOCK = threading.Lock()


def parse_formula(source: str):
    """Parse only the prover's constructor expression language, without eval()."""
    if not isinstance(source, str) or not source.strip():
        raise ValueError("Formula is required.")
    if len(source) > 4000:
        raise ValueError("Formula is too long.")

    try:
        tree = ast.parse(source.strip(), mode="eval")
    except SyntaxError as exc:
        raise ValueError(f"Syntax error near column {exc.offset or '?'}.") from exc

    def build(node: ast.AST, depth: int = 0):
        if depth > 100:
            raise ValueError("Formula nesting is too deep.")
        if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name):
            raise ValueError("Use constructors such as Prop('p'), Imp(...), Box(...).")
        name = node.func.id
        if name not in CONSTRUCTORS:
            raise ValueError(f"Unknown constructor: {name}")
        if node.keywords:
            raise ValueError("Keyword arguments are not supported.")
        expected = ARITY[name]
        if len(node.args) != expected:
            raise ValueError(f"{name} expects {expected} argument(s).")

        if name == "Prop":
            arg = node.args[0]
            if not isinstance(arg, ast.Constant) or not isinstance(arg.value, str):
                raise ValueError("Prop expects a quoted name, for example Prop('p').")
            value = arg.value.strip()
            if not value or len(value) > 80:
                raise ValueError("Proposition names must contain 1–80 characters.")
            return Prop(value)

        args = [build(arg, depth + 1) for arg in node.args]
        return CONSTRUCTORS[name](*args)

    return build(tree.body)


def compile_tex_files(run_dir: Path) -> list[str]:
    if shutil.which("pdflatex") is None:
        return []
    generated = []
    for tex_path in sorted(run_dir.glob("*.tex")):
        proc = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", tex_path.name],
            cwd=run_dir,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=40,
            check=False,
        )
        pdf_path = tex_path.with_suffix(".pdf")
        if proc.returncode == 0 and pdf_path.exists():
            generated.append(pdf_path.name)
    return generated


def run_prover(formula_source: str, compile_pdf: bool) -> dict:
    formula = parse_formula(formula_source)
    run_id = uuid.uuid4().hex
    # Only the newest result is retained. This prevents web/runs from growing indefinitely.
    clear_runs()
    run_dir = RUNS_DIR / run_id
    run_dir.mkdir(parents=True)

    output = io.StringIO()
    old_cwd = Path.cwd()
    try:
        # The original prover writes fixed filenames in cwd, so serialize runs.
        with PROOF_LOCK, contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            os.chdir(run_dir)
            provable = proof_search_visual(formula)
    finally:
        os.chdir(old_cwd)

    pdfs = compile_tex_files(run_dir) if compile_pdf else []
    countermodel_pdf_error = None
    countermodel_pdf_url = None
    if not provable:
        countermodel_tex = run_dir / "countermodel.tex"
        if not countermodel_tex.exists():
            countermodel_pdf_error = "The prover did not generate countermodel.tex."
        elif shutil.which("pdflatex") is None:
            countermodel_pdf_error = "Install pdflatex to compile the generated countermodel.tex file."
        elif "countermodel.pdf" not in pdfs:
            proc = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", countermodel_tex.name],
                cwd=run_dir,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=40,
                check=False,
            )
            if proc.returncode == 0 and (run_dir / "countermodel.pdf").exists():
                pdfs.append("countermodel.pdf")
            else:
                countermodel_pdf_error = "countermodel.tex was generated, but LaTeX could not compile it."
        if (run_dir / "countermodel.pdf").exists():
            countermodel_pdf_url = f"/runs/{run_id}/countermodel.pdf"

    remove_latex_auxiliary_files(run_dir)

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
        "formula": str(formula),
        "provable": bool(provable),
        "output": output.getvalue(),
        "artifacts": artifacts,
        "pdf_available": shutil.which("pdflatex") is not None,
        "countermodel_pdf_url": countermodel_pdf_url,
        "countermodel_pdf_error": countermodel_pdf_error,
    }


class Handler(SimpleHTTPRequestHandler):
    server_version = "labIKsLocal/1.0"

    def log_message(self, fmt: str, *args):
        print(f"[web] {self.address_string()} - {fmt % args}")

    def send_json(self, payload: dict, status: int = 200):
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
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
        except Exception as exc:
            traceback.print_exc()
            self.send_json({"ok": False, "error": f"Prover failed: {exc}"}, 500)

    def do_GET(self):
        path = unquote(urlparse(self.path).path)
        if path == "/":
            return self.serve_file(STATIC_DIR / "index.html")
        if path.startswith("/static/"):
            rel = Path(path.removeprefix("/static/"))
            return self.serve_safe(STATIC_DIR, rel)
        if path.startswith("/runs/"):
            rel = Path(path.removeprefix("/runs/"))
            return self.serve_safe(RUNS_DIR, rel, attachment=True)
        if path == "/api/health":
            return self.send_json({"ok": True, "pdf_available": shutil.which("pdflatex") is not None})
        self.send_error(HTTPStatus.NOT_FOUND)

    def serve_safe(self, base: Path, rel: Path, attachment: bool = False):
        target = (base / rel).resolve()
        try:
            target.relative_to(base.resolve())
        except ValueError:
            self.send_error(HTTPStatus.FORBIDDEN)
            return
        self.serve_file(target, attachment=attachment)

    def serve_file(self, path: Path, attachment: bool = False):
        if not path.is_file():
            self.send_error(HTTPStatus.NOT_FOUND)
            return
        data = path.read_bytes()
        content_type = mimetypes.guess_type(path.name)[0] or "application/octet-stream"
        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        if attachment:
            self.send_header("Content-Disposition", f'inline; filename="{path.name}"')
        self.end_headers()
        self.wfile.write(data)


def main():
    # Clear artifacts left by an earlier server session.
    clear_runs()
    host = os.environ.get("LABIKS_HOST", "127.0.0.1")
    port = int(os.environ.get("LABIKS_PORT", "8000"))
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
