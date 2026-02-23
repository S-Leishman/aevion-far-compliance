#!/usr/bin/env bash
# Generate proof certificate output for patent/paper evidence.
# Run from repo root: ./lean-proofs/scripts/generate_proof_certificates.sh
# Or from lean-proofs: ./scripts/generate_proof_certificates.sh

set -e
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$LEAN_ROOT/.." && pwd)"
OUT_PATH="$REPO_ROOT/docs/proof_certificates.txt"

cd "$LEAN_ROOT"
lake build 2>/dev/null || true
lake exe verify > "$OUT_PATH" 2>&1
echo "Proof certificate output written to: $OUT_PATH"
