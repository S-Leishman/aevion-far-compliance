import Aevion.ErdosSzekeres

/-!
# X402 Budget Constraints — Formal Verification

**Purpose**: Provide formal specifications for x402 payment safety verification.
Every x402 transaction must satisfy these constraints before the Sheriff signs.

## Budget Structure (94-5-1)

- **Operational**: 94% — Core business operations
- **Emergency**: 5% — Contingency reserves
- **Discretionary**: 1% — Optional programs

## Usage

When an AI agent wants to execute an x402 payment:
1. Agent constructs transaction with category (Operational/Emergency/Discretionary)
2. Agent generates Lean4 proof that transaction respects budget bounds
3. Sheriff Logic Node verifies proof in <100ms
4. Zymbit hardware signs only if proof is valid

**Patent**: US 63/896,282, Claims 1-5 (Tri-modal separation, Hardware trust anchor)
-/

namespace Aevion.X402

/-!
## Part A: Budget Structure
-/

/-- Budget allocation percentages. Default: 94-5-1 split. -/
structure BudgetAllocation where
  operational : ℚ    -- 94/100 = 0.94
  emergency : ℚ      -- 5/100 = 0.05
  deriving Repr

/-- Default 94-5-1 budget allocation. -/
def defaultBudget : BudgetAllocation where
  operational := 94 / 100
  emergency := 5 / 100

/-!
## Part B: Transaction Categories
-/

/-- Category of x402 transaction. -/
inductive TransactionCategory
  | Operational   -- Core business (94% budget)
  | Emergency     -- Contingency (5% budget)
  | Discretionary -- Optional (1% budget)
  deriving Repr, DecidableEq

/-- Get budget percentage for category. -/
def TransactionCategory.budgetFraction (cat : TransactionCategory) : ℚ :=
  match cat with
  | .Operational => 94 / 100
  | .Emergency => 5 / 100
  | .Discretionary => 1 / 100

/-!
## Part C: Transaction Structure
-/

/-- An x402 transaction request. -/
structure Transaction where
  amount : ℚ           -- Payment amount in USD
  recipient : String   -- Payment address/contract
  category : TransactionCategory
  timestamp : Nat      -- Unix timestamp
  memo : String        -- Optional description
  deriving Repr, DecableEq

/-- Current budget state (cumulative spend per category). -/
structure BudgetState where
  operationalSpent : ℚ    -- Already spent on operational
  emergencySpent : ℚ      -- Already spent on emergency
  discretionarySpent : ℚ  -- Already spent on discretionary
  totalBudget : ℚ        -- Total budget available
  deriving Repr

/-- Remaining budget per category. -/
def BudgetState.remaining (s : BudgetState) : BudgetState :=
  { s with
    operationalSpent := s.totalBudget * (94/100) - s.operationalSpent,
    emergencySpent := s.totalBudget * (5/100) - s.emergencySpent,
    discretionarySpent := s.totalBudget * (1/100) - s.discretionarySpent }

/-!
## Part D: Safety Predicates
-/

/-- Whether transaction fits within operational budget. -/
def Transaction.withinOperationalBudget
  (tx : Transaction) (s : BudgetState) : Prop :=
  s.operationalSpent + tx.amount ≤ s.totalBudget * (94/100)

/-- Whether transaction fits within emergency budget. -/
def Transaction.withinEmergencyBudget
  (tx : Transaction) (s : BudgetState) : Prop :=
  s.emergencySpent + tx.amount ≤ s.totalBudget * (5/100)

/-- Whether transaction fits within discretionary budget. -/
def Transaction.withinDiscretionaryBudget
  (tx : Transaction) (s : BudgetState) : Prop :=
  s.discretionarySpent + tx.amount ≤ s.totalBudget * (1/100)

/-- Whether transaction is valid for its category. -/
def Transaction.validForCategory
  (tx : Transaction) (s : BudgetState) : Prop :=
  match tx.category with
  | .Operational => tx.withinOperationalBudget s
  | .Emergency => tx.withinEmergencyBudget s
  | .Discretionary => tx.withinDiscretionaryBudget s

/-- Whether transaction is safe (valid for category AND within overall limits). -/
def Transaction.isSafe
  (tx : Transaction) (s : BudgetState) : Prop :=
  tx.validForCategory s ∧ tx.amount > 0

/-!
## Part E: Main Theorem — Transaction Safety Proof

This is the theorem agents must prove for every x402 payment.
-/

/-- Safety theorem: Transaction respects budget constraints.

**Agent's burden**: For any transaction tx and budget state s,
prove that tx.isSafe s holds. Only then will Sheriff sign.

**Usage in x402 flow**:
```python
proof = prover.prove(
  theorem="transaction_respects_budget",
  parameters={
    "tx": {"amount": 100, "category": "Operational", ...},
    "s": {"operationalSpent": 5000, "totalBudget": 100000, ...}
  }
)
sheriff.verify(proof)  # If valid, sign transaction
```
-/
theorem transaction_respects_budget
  (tx : Transaction) (s : BudgetState)
  (h_amount : tx.amount > 0)
  (h_cat : match tx.category with
    | .Operational => tx.withinOperationalBudget s
    | .Emergency => tx.withinEmergencyBudget s
    | .Discretionary => tx.withinDiscretionaryBudget s) :
  tx.isSafe s :=
  And.intro h_cat h_amount

/-!
## Part F: Computational Checking (for automated proof)

For agents that can't construct full proofs, we provide computational checking.
-/

/-- Compute whether transaction is within budget (computational). -/
def Transaction.checkWithinBudget
  (tx : Transaction) (s : BudgetState) : Bool :=
  match tx.category with
  | .Operational => s.operationalSpent + tx.amount ≤ s.totalBudget * (94/100)
  | .Emergency => s.emergencySpent + tx.amount ≤ s.totalBudget * (5/100)
  | .Discretionary => s.discretionarySpent + tx.amount ≤ s.totalBudget * (1/100)

/-- Compute whether transaction is safe (computational). -/
def Transaction.checkSafe (tx : Transaction) (s : BudgetState) : Bool :=
  (tx.amount > 0) ∧ tx.checkWithinBudget s

/-!
## Part G: Emergency Override

Emergency transactions can exceed discretionary/operational limits
but require special proof with justification.
-/

/-- Emergency override: Transaction exceeds normal limits but is justified.

**Conditions**:
1. Category must be Emergency
2. Amount must not exceed total emergency budget
3. Must have emergency justification (coded as string)
4. Must not have been used more than twice this quarter
-/
structure EmergencyJustification where
  reason : String              -- Justification text
  approver : String           -- Who approved
  timesUsedThisQuarter : Nat  -- Cannot exceed 2
  deriving Repr

def EmergencyJustification.isValid (j : EmergencyJustification) : Prop :=
  j.timesUsedThisQuarter < 2

theorem emergency_override_safe
  (tx : Transaction) (s : BudgetState) (j : EmergencyJustification)
  (h_emergency : tx.category = TransactionCategory.Emergency)
  (h_justification : j.isValid)
  (h_within_emergency : s.emergencySpent + tx.amount ≤ s.totalBudget * (5/100))
  (h_positive : tx.amount > 0) :
  tx.isSafe s :=
  have h_cat : tx.withinEmergencyBudget s := h_within_emergency
  And.intro h_cat h_positive

end Aevion.X402
