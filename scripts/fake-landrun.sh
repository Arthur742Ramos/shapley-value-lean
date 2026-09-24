#!/usr/bin/env bash
set -euo pipefail

while [ "$#" -gt 0 ] && [ "$1" != "--" ]; do
  shift
done
if [ "$#" -eq 0 ]; then
  echo "error: fake Landrun received no command" >&2
  exit 2
fi
shift
exec "$@"
