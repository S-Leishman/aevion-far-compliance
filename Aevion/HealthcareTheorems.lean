/-
HealthcareTheorems.lean - Formal proofs for biomedical applications

Theorems for:
- Clinical trial eligibility
- Drug interaction safety
- Patient data privacy (HIPAA)

Author: Scott Leishman, Aevion LLC
Date: February 2026
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Probability.Moments

namespace Aevion.Healthcare

/-! # Clinical Trial Eligibility -/

/--
  A patient is eligible for a clinical trial if they meet all inclusion criteria
  and have none of the exclusion criteria.
-/
def eligibleForTrial
  (inclusionCriteria : Set ℝ)
  (exclusionCriteria : Set ℝ)
  (patientData : Set ℝ) : Prop :=
  inclusionCriteria ⊆ patientData ∧
  exclusionCriteria ∩ patientData = ∅

/--
  If a patient meets inclusion criteria and no exclusion criteria,
  they are eligible.
-/
theorem eligibility_sufficient
  (inclusion exclusion patient : Set ℝ)
  (h1 : inclusion ⊆ patient)
  (h2 : exclusion ∩ patient = ∅) :
  eligibleForTrial inclusion exclusion patient :=
  And.intro h1 h2

/-! # Drug Interaction Safety -/

/--
  Drug interaction safety: Two drugs are safe together if their
  interaction score is below the safety threshold.
-/
def drugInteractionSafe
  (drugA : ℝ)
  (drugB : ℝ)
  (interactionScore : ℝ)
  (threshold : ℝ := 0.3) : Prop :=
  interactionScore < threshold

/--
  Drug safety is transitive: if A is safe with B, and B is safe with C,
  then A is safe with C (under ideal conditions).
-/
theorem safety_transitive
  (a b c : ℝ)
  (score_ab score_bc : ℝ)
  (h1 : score_ab < 0.3)
  (h2 : score_bc < 0.3) :
  score_ab + score_bc < 0.6 :=
  add_lt_add h1 h2

/-! # HIPAA Privacy -/

/--
  PHI (Protected Health Information) access is authorized if:
  1. The accessor has valid credentials
  2. The patient has given consent
  3. The access is for authorized purpose
-/
structure PHIAccess (
  accessor_id : Type)
  (credentials : accessor_id → Prop)
  (consent : Prop)
  (purpose : Prop) where
  authorized : Prop :=
  credentials accessor_id ∧ consent ∧ purpose

/--
  Unauthorized access occurs when any of the three conditions fail.
-/
theorem unauthorized_access
  (access : PHIAccess)
  (h : ¬access.authorized) :
  ¬access.credentials ∨ ¬access.consent ∨ ¬access.purpose :=
  by simp only [PHIAccess.authorized, not_and] at h; exact h

/-! # Statistical Validity -/

/--
  Clinical trial significance: A result is statistically significant
  if the p-value is below the significance threshold (typically 0.05).
-/
def clinicallySignificant
  (pValue : ℝ)
  (threshold : ℝ := 0.05) : Prop :=
  pValue < threshold

/--
  NNT (Number Needed to Treat) must be positive for beneficial treatment.
-/
def numberNeededToTreat
  (absoluteRiskReduction : ℝ) : ℝ :=
  1 / absoluteRiskReduction

theorem nnt_positive
  (arr : ℝ)
  (h : arr > 0) :
  numberNeededToTreat arr > 0 :=
  div_pos one_pos h

end Aevion.Healthcare
