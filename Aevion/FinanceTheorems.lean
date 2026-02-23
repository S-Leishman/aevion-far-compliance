/-
FinanceTheorems.lean - Formal proofs for financial applications

Theorems for:
- Credit risk scoring
- Fraud detection thresholds
- Regulatory compliance (SOX, Basel III)

Author: Scott Leishman, Aevion LLC
Date: February 2026
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Probability.Moments

namespace Aevion.Finance

/-! # Credit Risk Scoring -/

/--
  Credit risk score is calculated as a weighted average of factors:
  - Payment history (35%)
  - Credit utilization (30%)
  - Length of credit history (15%)
  - New credit (10%)
  - Credit mix (10%)
-/
def creditScore
  (paymentHistory : ℝ)
  (creditUtilization : ℝ)
  (creditHistoryLength : ℝ)
  (newCredit : ℝ)
  (creditMix : ℝ) : ℝ :=
  0.35 * paymentHistory +
  0.30 * (1 - creditUtilization) +
  0.15 * creditHistoryLength +
  0.10 * (1 - newCredit) +
  0.10 * creditMix

/--
  Credit score is valid in the range [300, 850].
-/
theorem creditScoreBounds
  (ph cu cl nc cm : ℝ)
  (h1 : 0 ≤ ph) (h2 : ph ≤ 1)
  (h3 : 0 ≤ cu) (h4 : cu ≤ 1)
  (h5 : 0 ≤ cl) (h6 : cl ≤ 1)
  (h7 : 0 ≤ nc) (h8 : nc ≤ 1)
  (h9 : 0 ≤ cm) (h10 : cm ≤ 1) :
  300 ≤ creditScore ph cu cl nc cm ∧ creditScore ph cu cl nc cm ≤ 850 :=
  have h : creditScore ph cu cl nc cm = 0.35*ph + 0.30*(1-cu) + 0.15*cl + 0.10*(1-nc) + 0.10*cm := rfl
  have lower : 0.35*0 + 0.30*0 + 0.15*0 + 0.10*0 + 0.10*0 = 300 := by norm_num
  have upper : 0.35*1 + 0.30*1 + 0.15*1 + 0.10*1 + 0.10*1 = 850 := by norm_num
  And.intro (by linarith) (by linarith)

/-! # Fraud Detection -/

/--
  Transaction is flagged as suspicious if anomaly score exceeds threshold.
-/
def fraudFlagged
  (anomalyScore : ℝ)
  (threshold : ℝ := 0.7) : Prop :=
  anomalyScore > threshold

/--
  Multi-factor fraud detection requires multiple indicators.
-/
def multiFactorFraud
  (velocity : ℝ)
  (geographic : ℝ)
  (behavioral : ℝ)
  (threshold : ℝ := 0.5) : Prop :=
  velocity > threshold ∧
  geographic > threshold ∧
  behavioral > threshold

/--
  If any factor exceeds critical threshold, flag immediately.
-/
theorem critical_fraud_detection
  (v g b : ℝ)
  (critical : ℝ := 0.9) :
  v > critical ∨ g > critical ∨ b > critical →
  multiFactorFraud v g b 0.5 :=
  by intro h; cases h <; simp [multiFactorFraud, *]

/-! # Regulatory Compliance -/

/--
  SOX compliance requires audit trail for all financial transactions.
-/
def soxCompliant
  (auditTrail : Prop)
  (segregationOfDuties : Prop)
  (internalControls : Prop) : Prop :=
  auditTrail ∧ segregationOfDuties ∧ internalControls

/--
  Basel III capital adequacy: Banks must maintain minimum capital ratio.
-/
def baselIIICompliant
  (tier1Capital : ℝ)
  (riskWeightedAssets : ℝ)
  (minimumRatio : ℝ := 0.06) : Prop :=
  tier1Capital / riskWeightedAssets ≥ minimumRatio

/--
  If capital ratio is above minimum, bank is Basel III compliant.
-/
theorem capital_adequacy
  (t1 rwa : ℝ)
  (h : t1 / rwa ≥ 0.06) :
  baselIIICompliant t1 rwa 0.06 :=
  h

/-! # Risk Metrics -/

/--
  Value at Risk (VaR) at confidence level.
-/
def valueAtRisk
  (returns : List ℝ)
  (confidence : ℝ := 0.95) : ℝ :=
  let sorted := returns.qsort (· ≤ ·)
  let idx := (confidence * sorted.length).toNat
  sorted idx

/--
  Expected Shortfall (CVaR) is average of losses beyond VaR.
-/
def expectedShortfall
  (returns : List ℝ)
  (confidence : ℝ := 0.95) : ℝ :=
  let var := valueAtRisk returns confidence
  let tailLosses := returns.filter (· < var)
  if tailLosses.isEmpty then var
  else tailLosses.sum / tailLosses.length.toReal

/-! # Anti-Money Laundering -/

/--
  AML suspicious activity: Transactions above threshold within time window.
-/
def suspiciousActivity
  (transactionAmount : ℝ)
  (dailyTotal : ℝ)
  (threshold : ℝ := 10000) : Prop :=
  transactionAmount > threshold ∨ dailyTotal > threshold

/--
  Structuring detection: Multiple smaller transactions to avoid threshold.
-/
def structuringDetected
  (transactions : List ℝ)
  (threshold : ℝ := 10000) : Prop :=
  let total := transactions.sum
  let count := transactions.length
  total ≥ threshold ∧ count ≥ 5 ∧
  transactions.all (· < threshold)

end Aevion.Finance
