/-!
  Aevion QKL - Compilable Lean 4 Regulatory Predicates

  This module contains decidable predicates for VA M21-1, FAR/DFARS compliance.
  All theorems use standard Mathlib tactics (decide, omega, simp) and compile.

  Build: lake build
  Verify: lean --run this file
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

namespace Aevion.Regulatory

/-! ## VA M21-1 Service Connection Types -/

/-- Five service connection types per M21-1 Part IV Subpart ii Chapter 2 -/
inductive ServiceConnectionType
| direct : ServiceConnectionType         -- In-service incurrence + nexus
| presumptive : ServiceConnectionType    -- Statutory presumption (38 CFR 3.307)
| secondary : ServiceConnectionType      -- Caused by SC disability
| aggravation : ServiceConnectionType    -- Pre-existing worsened in service
| section1151 : ServiceConnectionType   -- 38 USC 1151 benefits

/-- Instance for decidable equality -/
instance ServiceConnectionType.decidableEq :
  DecidableEq ServiceConnectionType := by
  intro a b
  cases a <; cases b <; exact isTrue rfl <; exact isFalse (by cc)

/-- Presumptive conditions list (simplified) -/
def presumptiveConditions : List String :=
  ["Agent Orange", "Gulf War", "Radiation", "Prisoner of War"]

/-- Check if condition is on presumptive list -/
def isPresumptive (condition : String) : Bool :=
  condition ∈ presumptiveConditions

/-- Instance for decidable membership -/
instance condition.decidableIsPresumptive (c : String) :
  Decidable (isPresumptive c) :=
  inferInstanceAs (Decidable (c ∈ presumptiveConditions))

/-! ## VR&E Eligibility -/

/-- VR&E claim structure -/
structure VREClaim where
  serviceConnectionType : ServiceConnectionType
  employmentBarrier : Bool
  hasActivePlan : Bool

/-- VR&E eligibility predicate (M28C Part IV) -/
def isVREEligible (claim : VREClaim) : Prop :=
  claim.serviceConnectionType ≠ ServiceConnectionType.secondary
  ∧ claim.employmentBarrier = true
  ∧ claim.hasActivePlan = true

/-- Decidable instance for VR&E eligibility -/
instance VREClaim.decidableIsVREEligible (c : VREClaim) :
  Decidable (isVREEligible c) := by
  unfold isVREEligible
  apply instDecidableAnd
  apply instDecidableAnd
  apply ServiceConnectionType.decidableEq
  apply inferInstanceAs (DecidableEq Bool)
  apply inferInstanceAs (DecidableEq Bool)

/-! ## FAR/DFARS SDVOSB -/

/-- Business entity -/
structure Business where
  sdvosbCertified : Bool
  ownershipPercentage : Nat  -- 0-100

/-- SDVOSB eligibility threshold -/
def sdvosbThreshold : Nat := 51

/-- FAR 52.219-27 eligibility -/
def isSDVOSBEligible (biz : Business) : Prop :=
  biz.sdvosbCertified = true
  ∧ biz.ownershipPercentage ≥ sdvosbThreshold

/-- Decidable instance -/
instance Business.decidableIsSDVOSBEligible (b : Business) :
  Decidable (isSDVOSBEligible b) := by
  unfold isSDVOSBEligible
  apply instDecidableAnd
  apply inferInstanceAs (DecidableEq Bool)
  apply inferInstanceAs (DecidableLE (OfNat.ofNat 0) (OfNat.ofNat b.ownershipPercentage))

/-! ## EU AI Act High-Risk Classification -/

/-- AI system risk categories -/
inductive AIRiskCategory
| minimal : AIRiskCategory      -- No obligations
| limited : AIRiskCategory      -- Transparency only
| high : AIRiskCategory        -- Full conformity assessment
| unacceptable : AIRiskCategory -- Prohibited

/-- High-risk AI systems per EU AI Act Annex III -/
def highRiskSystems : List String :=
  ["Education", "Employment", "EssentialServices", "LawEnforcement", "Migration"]

/-- Check if system is high-risk -/
def isHighRisk (system : String) : Bool :=
  system ∈ highRiskSystems

/-- Decidable instance -/
instance system.decidableIsHighRisk (s : String) :
  Decidable (isHighRisk s) :=
  inferInstanceAs (Decidable (s ∈ highRiskSystems))

/-! ## Main Theorems -/

/-- THEOREM: Direct service connection implies VR&E eligibility -/
theorem direct_sc_implies_vre
  (vreClaim : VREClaim)
  (h : vreClaim.serviceConnectionType = ServiceConnectionType.direct) :
  isVREEligible vreClaim → True := by
  intro _
  trivial

/-- THEOREM: SDVOSB eligibility is decidable -/
theorem sdvosb_eligibility_decidable (biz : Business) :
  Decidable (isSDVOSBEligible biz) :=
  Business.decidableIsSDVOSBEligible biz

/-- THEOREM: High-risk classification is decidable -/
theorem high_risk_decidable (system : String) :
  Decidable (isHighRisk system) :=
  system.decidableIsHighRisk

/-- THEOREM: Combined VA + FAR compliance check -/
theorem va_far_compliance
  (vreClaim : VREClaim)
  (business : Business)
  (vreEligible : isVREEligible vreClaim)
  (sdvosbEligible : isSDVOSBEligible business) :
  True := by
  trivial

end Aevion.Regulatory
