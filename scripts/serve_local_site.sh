#!/usr/bin/env bash

set -euo pipefail

port="${1:-8000}"
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
preview_dir="$repo_root/build/site-preview"

if ! command -v bundle >/dev/null 2>&1; then
  echo "bundle is required to build the local homepage preview."
  echo "Run bundle install in home_page first."
  exit 1
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "python3 is required to serve the local preview."
  exit 1
fi

if [ ! -f "$repo_root/.lake/build/doc/index.html" ]; then
  echo "API docs are missing. Run: lake build TwoControl:docs"
  exit 1
fi

if [ ! -f "$repo_root/blueprint/web/index.html" ]; then
  echo "Blueprint web output is missing. Run: leanblueprint web"
  exit 1
fi

mkdir -p "$preview_dir"

(
  cd "$repo_root/home_page"
  bundle exec jekyll build --destination "$preview_dir"
)

rm -rf "$preview_dir/docs" "$preview_dir/blueprint"
cp -R "$repo_root/.lake/build/doc" "$preview_dir/docs"
cp -R "$repo_root/blueprint/web" "$preview_dir/blueprint"

if [ -f "$repo_root/blueprint/print/print.pdf" ]; then
  cp "$repo_root/blueprint/print/print.pdf" "$preview_dir/blueprint.pdf"
fi

echo "Serving local site at http://127.0.0.1:$port"
cd "$preview_dir"
python3 -m http.server "$port"