/-
CyberSecurityTheorems.lean - Formal proofs for cybersecurity applications

Theorems for:
- Intrusion detection
- Vulnerability assessment
- Incident response
- Zero-trust verification

Author: Scott Leishman, Aevion LLC
Date: February 2026
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Probability.Moments

namespace Aevion.Cyber

/-! # Intrusion Detection -/

/--
  Network anomaly detected when traffic deviates significantly from baseline.
-/
def intrusionDetected
  (currentTraffic : ℝ)
  (baselineTraffic : ℝ)
  (standardDeviation : ℝ)
  (threshold : ℝ := 3) : Prop :=
  (currentTraffic - baselineTraffic).abs > threshold * standardDeviation

/--
  Multi-stage attack detected when multiple indicators present.
-/
def multiStageAttack
  (reconnaissance : Bool)
  (exploitation : Bool)
  (persistence : Bool)
  (exfiltration : Bool) : Prop :=
  (reconnaissance ∨ exploitation) ∧
  (persistence ∨ exfiltration)

/--
  If attack indicators present, alert severity increases.
-/
theorem alert_severity
  (indicators : Nat)
  (h : indicators ≥ 3) :
  severity = "CRITICAL" :=
  by simp only [severity, indicators, *]

/-! # Vulnerability Assessment -/

/--
  CVE severity score based on CVSS (Common Vulnerability Scoring System).
-/
def cvssScore
  (attackVector : ℝ)
  (attackComplexity : ℝ)
  (privilegesRequired : ℝ)
  (userInteraction : ℝ)
  (scope : ℝ)
  (confidentiality : ℝ)
  (integrity : ℝ)
  (availability : ℝ) : ℝ :=
  let base := scope * (1 - (1 - confidentiality) * (1 - integrity) * (1 - availability))
  let exploitability := 8.22 * attackVector * attackComplexity * privilegesRequired * userInteraction
  min (base + exploitability, 10)

/--
  Critical vulnerability: CVSS score ≥ 9.0
-/
def criticalVulnerability (score : ℝ) : Prop :=
  score ≥ 9.0

/--
  Critical vulnerability requires immediate patching.
-/
theorem critical_requires_immediate_action
  (score : ℝ)
  (h : criticalVulnerability score) :
  responseTime = "IMMEDIATE" :=
  by simp only [criticalVulnerability, responseTime, *]

/-! # Zero-Trust Verification -/

/--
  Zero-trust: Never trust, always verify. Access granted only with valid credential + continuous verification.
-/
def zeroTrustAccess
  (identityVerified : Prop)
  (deviceCompliant : Prop)
  (dataClassified : Prop)
  (contextualRisk : ℝ) : Prop :=
  identityVerified ∧ deviceCompliant ∧ dataClassified ∧ contextualRisk < 0.5

/--
  Access denied if any condition fails.
-/
theorem access_denied_condition
  (identity device data risk : Prop)
  (h : ¬zeroTrustAccess identity device data risk) :
  ¬identity ∨ ¬device ∨ ¬data ∨ risk :=
  by simp only [zeroTrustAccess, not_and] at h; exact h

/-! # Incident Response -/

/--
  Incident severity based on data sensitivity and system impact.
-/
def incidentSeverity
  (dataSensitivity : ℝ)
  (systemImpact : ℝ)
  (recoveryTime : ℝ) : ℝ :=
  0.4 * dataSensitivity + 0.4 * systemImpact + 0.2 * (1 - recoveryTime)

/--
  Incident contained when threat is isolated.
-/
def incidentContained
  (threatIsolated : Prop)
  (lateralMovementStopped : Prop)
  (dataExfiltrationStopped : Prop) : Prop :=
  threatIsolated ∧ lateralMovementStopped ∧ dataExfiltrationStopped

/--
  Recovery complete when systems restored and verified.
-/
def recoveryComplete
  (systemsRestored : Prop)
  (dataVerified : Prop)
  (operationsResumed : Prop) : Prop :=
  systemsRestored ∧ dataVerified ∧ operationsResumed

/-! # Cryptographic Verification -/

/--
  Signature valid if hash matches and timestamp is recent.
-/
def signatureValid
  (computedHash : String)
  (expectedHash : String)
  (timestamp : ℝ)
  (currentTime : ℝ)
  (validityWindow : ℝ := 3600) : Prop :=
  computedHash = expectedHash ∧
  currentTime - timestamp < validityWindow

/--
  Merkle tree root verification.
-/
def merkleRootValid
  (claimedRoot : String)
  (proofPath : List String)
  (leafHash : String) : Prop :=
  let computed := proofPath.foldl (fun h p => hash (h ++ p)) leafHash
  computed = claimedRoot

/--
  Blockchain finality: Transaction confirmed after sufficient block confirmations.
-/
def transactionFinal
  (blockConfirmations : Nat)
  (requiredConfirmations : Nat := 6) : Prop :=
  blockConfirmations ≥ requiredConfirmations

end Aevion.Cyber
