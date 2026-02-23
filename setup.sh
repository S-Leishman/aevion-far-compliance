#!/bin/bash
# Setup script for Aevion FAR Compliance Proofs
# Install Lean 4 and build the project

set -e

echo "Installing Lean 4 via elan..."

# Install elan (Lean version manager)
curl --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Source elan
source "$HOME/.elan/bin/activate"

# Install Lean 4 toolchain
elan toolchain install nightly

# Build the project
echo "Building lean proofs..."
cd "$(dirname "$0")"

# Initialize lake if needed
if [ ! -f lakefile.lean ]; then
    lake init AevionProofs
fi

lake build

echo "Build complete!"
echo ""
echo "To verify FAR compliance:"
echo "  lean --run FARCompliance.lean"
echo ""
echo "To generate XGML certificates:"
echo "  python -m aevion.xgml_generator"
