import Aevion.NThreeOptimal
import Aevion.FPCComposition
import Aevion.ByzantineBounds
import Aevion.ResilienceFactor
import Aevion.ProbabilisticResilience
import Aevion.LegalTheorems
import Aevion.ContractEnforcement
import Aevion.SemanticTriplets
import Aevion.XGMLProperties
import Aevion.VarianceHalt
import Aevion.ProviderDiversity
import Aevion.ErdosSzekeres
import Aevion.ArithmeticKakeya
import Aevion.LargeSteiner
import Aevion.ChainOfThoughtBounds

/-!
# Aevion Formal Verification Library

Mathematical proofs for Byzantine AI consensus using Lean 4.

## Modules (13 files)

### Original (7 files)
- `Aevion.NThreeOptimal`: N=3 optimality theorem for LLM ensembles
- `Aevion.FPCComposition`: Finite Provable Computation composition theorems
- `Aevion.ByzantineBounds`: Byzantine fault tolerance bounds
- `Aevion.ResilienceFactor`: Resilience factor calculations
- `Aevion.ProbabilisticResilience`: Why N=3 survives f=1 empirically
- `Aevion.LegalTheorems`: VA disability claim verification (38 CFR)
- `Aevion.ContractEnforcement`: SACL contract enforcement proofs

### New (5 files, Feb 10–12 2026)
- `Aevion.ErdosSzekeres`: Erdős–Szekeres structural entropy (RAHR H_struct)
- `Aevion.ArithmeticKakeya`: AK(1.75) + AK(1.675) push; Claim 9 combinatorial entropy routing
- `Aevion.LargeSteiner`: Steiner (64,8,6); Claim 10
- `Aevion.SemanticTriplets`: F27 triplet verification — weakest-link, domain thresholds, benchmarks
- `Aevion.XGMLProperties`: XGML DAG properties — PageRank, LTL, signatures, acyclicity
- `Aevion.VarianceHalt`: Constitutional Halt — sigma thresholds, MIL-STD-882E, state machine
- `Aevion.ProviderDiversity`: F28 cross-provider BFT — PDS, natural Byzantine resilience

## Evidence Base

- 8 verified benchmarks (GSM8K, TruthfulQA, MMLU-Physics, ARC, SciQ, GPQA, MMLU-Math, PromptInject)
- Consensus meets or exceeds best single model on 5/8 benchmarks
- 3 results statistically significant at p<0.05
- Natural Byzantine resilience: 67% provider failure, accuracy maintained
- 99.12% adversarial defense rate across 5,250 samples

## Patent: US 63/896,282

This library provides formal proof evidence for:
- Claims 1-3, 5, 10-23: Constitutional Halt & Variance Monitoring
- Claims 24-30: Hardware Root-of-Trust
- Claims 79-83: Semantic Triplet Verification (F27)
- Claims 84-86: Cross-Provider BFT (F28)
- XGML DAG dependent claims (83A-83D)

Copyright (c) 2026 Aevion LLC. All rights reserved.
-/
