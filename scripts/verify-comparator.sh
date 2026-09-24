#!/usr/bin/env bash
set -euo pipefail

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cache_root="$repository_root/.cache/palomar-comparator"
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

# These are the Palomar verifier pins used for the Lean 4.33.0 local replay.
comparator_commit=68a064109f01c08f47c8edc9f51d6a2bbffaa188
lean4export_commit=15f6055e299ad5b89345e533cc2192f4cc00f659
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for required_command in cargo git go lake python3; do
  command -v "$required_command" >/dev/null 2>&1 || {
    echo "error: $required_command is required for Comparator" >&2
    exit 1
  }
done

if [ "$(uname -s)" != "Linux" ] && [ "$(printenv PALOMAR_ALLOW_UNSANDBOXED_LOCAL || true)" != "1" ]; then
  echo "error: real Landrun requires Linux Landlock" >&2
  echo "set PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 for an explicit macOS local replay" >&2
  exit 1
fi

mkdir -p "$cache_root" "$bin_dir"

checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"
checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"

project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$export_toolchain" ]; then
  echo "error: project toolchain $project_toolchain does not match Lean4Export $export_toolchain" >&2
  exit 1
fi

GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"
(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$repository_root"
lake exe cache get

landrun_binary="$bin_dir/landrun"
if [ "$(uname -s)" != "Linux" ]; then
  landrun_binary="$repository_root/scripts/fake-landrun.sh"
  echo "warning: using the explicit unsandboxed macOS fallback; CI must use real Landrun" >&2
fi

PALOMAR_LANDRUN_BIN="$landrun_binary" \
COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
COMPARATOR_LANDRUN="$repository_root/scripts/landrun-wrapper.sh" \
  lake env "$comparator_dir/.lake/build/bin/comparator" comparator.json
