#!/usr/bin/env bash
set -euo pipefail

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repository_root"

# Lean/Elan live under $HOME/.elan on developer machines and in CI images.
if [ -d "$HOME/.elan/bin" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
command -v lake >/dev/null 2>&1 || {
  echo "error: 'lake' not found on PATH (looked in \$HOME/.elan/bin)" >&2
  exit 1
}

for required_file in \
  lean-toolchain lake-manifest.json formalization.yaml Challenge.lean Solution.lean \
  comparator.json LICENSE THIRD_PARTY_NOTICES.md; do
  if [ ! -f "$required_file" ] || [ -L "$required_file" ]; then
    echo "error: required Palomar file is missing or not regular: $required_file" >&2
    exit 1
  fi
done

python3 - "$repository_root" <<'PY'
import json
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])
lakefiles = [name for name in ("lakefile.toml", "lakefile.lean") if (root / name).exists()]
if lakefiles != ["lakefile.lean"]:
    raise SystemExit(f"error: expected exactly lakefile.lean, found {lakefiles}")

challenge = root / "Challenge.lean"
challenge_text = challenge.read_text(encoding="utf-8")
if challenge.stat().st_size > 100 * 1024 or len(challenge_text.splitlines()) > 1000:
    raise SystemExit("error: Challenge.lean exceeds the 100 KiB or 1,000-line cap")

expected_import_lines = [
    "import Mathlib.Data.Finset.Max",
    "import Mathlib.Data.Fintype.Pi",
    "import Mathlib.Algebra.BigOperators.GroupWithZero.Finset",
    "import Mathlib.Algebra.Order.BigOperators.Group.Finset",
    "import Mathlib.Data.Real.Basic",
    "import Mathlib.Tactic",
]
actual_import_lines = [
    line for line in challenge_text.splitlines() if line.startswith("import ")
]
if actual_import_lines != expected_import_lines or challenge_text.splitlines()[:6] != expected_import_lines:
    raise SystemExit(
        f"error: Challenge.lean must start with the exact six Mathlib imports; found {actual_import_lines}"
    )

challenge_holes = len(re.findall(r"^\s*sorry\s*$", challenge_text, re.MULTILINE))
if challenge_holes != 6:
    raise SystemExit(f"error: expected six deliberate Challenge holes, found {challenge_holes}")

try:
    comparator = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    raise SystemExit(f"error: comparator.json is invalid: {error}")

required_keys = {
    "challenge_module", "solution_module", "theorem_names", "definition_names",
    "permitted_axioms", "enable_nanoda",
}
if not isinstance(comparator, dict) or set(comparator) != required_keys:
    raise SystemExit("error: comparator.json has an invalid key set")
if comparator["challenge_module"] != "Challenge":
    raise SystemExit("error: comparator.json must use Challenge as its statement module")
if comparator["solution_module"] != "Solution":
    raise SystemExit("error: comparator.json must use Solution as its proof module")
if comparator["theorem_names"] != [
    "ShapleyValue.Palomar.shapley_characterization",
    "ShapleyValue.Palomar.shapleyValue_unique",
    "ShapleyValue.Palomar.shapleyValue_efficient",
    "ShapleyValue.Palomar.shapleyValue_symmetric",
    "ShapleyValue.Palomar.shapleyValue_nullPlayer",
    "ShapleyValue.Palomar.shapleyValue_additive",
]:
    raise SystemExit("error: comparator theorem surface does not match the Shapley statements")
if comparator["definition_names"] != [
    "ShapleyValue.Game",
    "ShapleyValue.weight",
    "ShapleyValue.shapleyValue",
    "ShapleyValue.Efficient",
    "ShapleyValue.Symmetric",
    "ShapleyValue.NullPlayer",
    "ShapleyValue.Additive",
]:
    raise SystemExit("error: comparator definition surface does not match the Shapley definitions")
if comparator["enable_nanoda"] is not True:
    raise SystemExit("error: comparator.json must enable NanoDa")
if not isinstance(comparator["permitted_axioms"], list) or not set(comparator["permitted_axioms"]) <= {
    "propext", "Quot.sound", "Classical.choice"
}:
    raise SystemExit("error: comparator.json contains an unsupported axiom")

solution = (root / "Solution.lean").read_text(encoding="utf-8")
if re.search(r"(^|[^A-Za-z0-9_])(sorry|admit|oops)([^A-Za-z0-9_]|$)", solution):
    raise SystemExit("error: Solution.lean contains a proof placeholder")
if re.search(r"^\s*(axiom|unsafe)\b", solution, re.MULTILINE):
    raise SystemExit("error: Solution.lean declares an axiom or unsafe definition")

print(f"Palomar package shape passed: Challenge {challenge.stat().st_size} bytes")
PY

challenge_dependencies=$(lake env lean --src-deps Challenge.lean)
while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*|*/.lake/packages/mathlib/*) ;;
    *)
      echo "error: Challenge import closure contains a non-allowlisted source: $dependency" >&2
      exit 1
      ;;
  esac
done <<< "$challenge_dependencies"

lake build

check_tmpdir=$(mktemp -d)
trap 'rm -rf -- "$check_tmpdir"' EXIT
check_file="$check_tmpdir/ComparatorNames.lean"
challenge_kinds_file="$check_tmpdir/ChallengeDeclarationKinds.lean"
solution_kinds_file="$check_tmpdir/SolutionDeclarationKinds.lean"
python3 - "$repository_root/comparator.json" "$check_file" <<'PY'
import json
import pathlib
import sys

comparator = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
names = comparator["theorem_names"] + comparator["definition_names"]
if not all(isinstance(name, str) for name in names):
    raise SystemExit("error: comparator names must be strings")

with open(sys.argv[2], "w", encoding="utf-8") as output:
    output.write("import Challenge\n\n")
    for name in names:
        output.write(f"#check @{name}\n")
PY
lake env lean "$check_file"

python3 - "$repository_root/comparator.json" "$challenge_kinds_file" "$solution_kinds_file" <<'PY'
import json
import pathlib
import sys

comparator = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
checks = [
    ("definition_names", "defnInfo"),
    ("theorem_names", "thmInfo"),
]

for module, output_path in (("Challenge", sys.argv[2]), ("Solution", sys.argv[3])):
    with open(output_path, "w", encoding="utf-8") as output:
        output.write(f"import {module}\n\nopen Lean\n\nrun_cmd do\n  let env ← getEnv\n")
        for key, expected_kind in checks:
            for name in comparator[key]:
                output.write(f"  match env.find? `{name} with\n")
                output.write(f"  | some (.{expected_kind} _) => logInfo m!\"{expected_kind}: {name}\"\n")
                output.write(f"  | some _ => throwError \"expected {expected_kind} for {name}\"\n")
                output.write(f"  | none => throwError \"missing declaration {name}\"\n")
PY
lake env lean "$challenge_kinds_file"
lake env lean "$solution_kinds_file"
rm -rf -- "$check_tmpdir"
trap - EXIT

audit_output=$(lake env lean scripts/AxiomAudit.lean 2>&1)
printf '%s\n' "$audit_output"
printf '%s\n' "$audit_output" | python3 scripts/check-axiom-report.py comparator.json

python3 - "$repository_root/formalization.yaml" <<'PY'
import sys
import yaml

path = sys.argv[1]
with open(path, encoding="utf-8") as handle:
    data = yaml.safe_load(handle)

def fail(message):
    raise SystemExit(f"error: {message}")

if not isinstance(data, dict):
    fail("formalization.yaml must be a mapping")
if data.get("version") != "v0.4":
    fail("metadata version must be v0.4")
project = data.get("project")
if not isinstance(project, dict):
    fail("project metadata is incomplete")
if not isinstance(project.get("name"), str) or not project["name"].strip():
    fail("project.name is missing")
if not isinstance(project.get("description"), str) or not project["description"].strip():
    fail("project.description is missing")
if not isinstance(project.get("authors"), list) or not project["authors"]:
    fail("project.authors is empty")
if not isinstance(project.get("responsible_maintainers"), list) or not project["responsible_maintainers"]:
    fail("project.responsible_maintainers is empty")
if project.get("license") != "BSD-3-Clause":
    fail("project.license must match the root LICENSE")
import os
notices_path = os.path.join(os.path.dirname(path), "THIRD_PARTY_NOTICES.md")
if not os.path.isfile(notices_path):
    fail("THIRD_PARTY_NOTICES.md is missing")
classification = data.get("classification")
if not isinstance(classification, dict) or not isinstance(classification.get("arxiv"), list) \
        or not isinstance(classification.get("msc2020"), list):
    fail("classification is incomplete")
sources = data.get("sources")
if not isinstance(sources, list) or not sources:
    fail("sources must be a nonempty array")
valid_relationships = {"formalizes", "adapts", "independently-proves", "background"}
invalid_relationships = {s.get("relationship") for s in sources if isinstance(s, dict)} - valid_relationships
if invalid_relationships:
    fail(f"sources contain invalid relationships: {sorted(map(str, invalid_relationships))}")
source_based_relationships = {"formalizes", "adapts", "independently-proves"}
shapley_doi = "https://doi.org/10.1515/9781400881970-018"
has_shapley_source = any(
    isinstance(s, dict)
    and s.get("relationship") in source_based_relationships
    and shapley_doi in (s.get("id"), s.get("location"))
    for s in sources
)
if not has_shapley_source:
    fail("no formalizes/adapts/independently-proves source cites Shapley's DOI")
automation = data.get("automation")
if not isinstance(automation, dict) or not isinstance(automation.get("methods"), list) \
        or not automation["methods"]:
    fail("automation.methods must be nonempty")
review = data.get("review")
if not isinstance(review, dict) or not isinstance(review.get("status"), str) \
        or not review["status"].strip():
    fail("review.status is missing")
print("formalization.yaml shape passed.")
PY

git diff --check
echo "Palomar preparation checks passed."
