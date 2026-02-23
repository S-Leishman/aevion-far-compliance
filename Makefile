# Lean 4 Aevion proof library
# Requires: elan, lake in PATH. From repo root: make lean-build (or cd lean-proofs && make)
.PHONY: help build build-math clean verify

help:
	@echo "Lean proofs (Aevion library)"
	@echo "  make build      - lake build Aevion (all 15 modules)"
	@echo "  make build-math - build ErdosSzekeres, ArithmeticKakeya, LargeSteiner only"
	@echo "  make clean      - remove .lake/build"
	@echo "  make verify     - run lake exe verify (if present)"

build:
	lake build Aevion
	@echo "Lean build complete (15 modules)"

build-math:
	lake build Aevion.ErdosSzekeres Aevion.ArithmeticKakeya Aevion.LargeSteiner
	@echo "Math conquest build complete"

clean:
	rm -rf .lake/build
	@echo "Lean build artifacts removed"

verify:
	@lake exe verify 2>/dev/null || echo "Run 'lake build Aevion' to verify; verify exe optional."
