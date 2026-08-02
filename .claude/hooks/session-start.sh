#!/usr/bin/env bash
# SessionStart hook: prepare the dev environment for Claude Code sessions.
# Installs the package (editable) with dev extras so `pytest` and the
# `es-verify` console script are available immediately.
set -euo pipefail

cd "$(dirname "$0")/../.."

echo "[session-start] Installing erdos-straus-attack (editable, with dev extras)..."
if python3 -m pip install -e ".[dev]" >/tmp/es-setup.log 2>&1; then
  echo "[session-start] Dependencies ready. Run 'python -m pytest' or 'es-verify' to sanity-check."
else
  echo "[session-start] pip install failed; see /tmp/es-setup.log" >&2
  tail -n 20 /tmp/es-setup.log >&2 || true
fi
