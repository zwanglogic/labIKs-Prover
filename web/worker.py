from __future__ import annotations

import contextlib
import io
import json
import os
import sys
import traceback
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROVER_DIR = ROOT / "prover"
if str(PROVER_DIR) not in sys.path:
    sys.path.insert(0, str(PROVER_DIR))

from search import proof_search_visual  # noqa: E402
from web.formula_parser import parse_formula  # noqa: E402


def main() -> int:
    if len(sys.argv) != 4:
        return 2

    input_path = Path(sys.argv[1]).resolve()
    result_path = Path(sys.argv[2]).resolve()
    run_dir = Path(sys.argv[3]).resolve()
    output = io.StringIO()

    try:
        payload = json.loads(input_path.read_text(encoding="utf-8"))
        formula = parse_formula(payload["formula"])
        run_dir.mkdir(parents=True, exist_ok=True)

        old_cwd = Path.cwd()
        try:
            os.chdir(run_dir)
            with contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
                provable = proof_search_visual(formula)
        finally:
            os.chdir(old_cwd)

        result = {
            "ok": True,
            "formula": str(formula),
            "provable": bool(provable),
            "output": output.getvalue(),
        }
    except Exception as exc:
        result = {
            "ok": False,
            "error": f"Prover failed: {exc}",
            "output": output.getvalue(),
            "traceback": traceback.format_exc(),
        }

    result_path.write_text(json.dumps(result, ensure_ascii=False), encoding="utf-8")
    return 0 if result.get("ok") else 1


if __name__ == "__main__":
    raise SystemExit(main())
