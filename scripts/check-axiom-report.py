"""Fail closed on missing reports, unexpected output, or unapproved axioms."""
import json
import re
import sys
from pathlib import Path


if len(sys.argv) != 2:
    raise SystemExit("usage: check-axiom-report.py comparator.json")

try:
    config = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    raise SystemExit(f"error: invalid Comparator config: {error}")

expected = set(config.get("theorem_names", [])) | {
    "ShapleyValue.shapley_characterization",
    "ShapleyValue.shapleyValue_unique",
    "ShapleyValue.shapleyValue_efficient",
    "ShapleyValue.shapleyValue_symmetric",
    "ShapleyValue.shapleyValue_nullPlayer",
    "ShapleyValue.shapleyValue_additive",
}
allowed = set(config.get("permitted_axioms", []))
text = sys.stdin.read()
pattern = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
seen = set()
for match in pattern.finditer(text):
    name, body = match.groups()
    if name in seen:
        raise SystemExit(f"error: duplicate axiom report for {name}")
    seen.add(name)
    axioms = {axiom.strip() for axiom in body.split(",") if axiom.strip()}
    unexpected = axioms - allowed
    if unexpected:
        raise SystemExit(f"error: {name} uses unapproved axioms: {sorted(unexpected)}")

if pattern.sub("", text).strip():
    raise SystemExit("error: unrecognized axiom report output")
if seen != expected:
    raise SystemExit(
        f"error: axiom report coverage mismatch: "
        f"missing={sorted(expected - seen)}, extra={sorted(seen - expected)}"
    )

print(f"Exact axiom allowlist passed for {len(seen)} declarations.")

