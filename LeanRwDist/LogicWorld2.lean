import Mathlib

/-!
# Logic World 2: Basic Tactics

Same theorem statements as `LogicWorld1`, but proved in tactic mode.
Focus tactics: `intro`, `apply`, `exact`, `rw` (plus basic case-splitting helpers).
-/

set_option autoImplicit false

namespace LeanRwDist
namespace LogicWorld2

section PropositionalLogic

variable (P Q R : Prop)
variable (a b c : Nat)

/-!
## Worked Examples (Basic Tactics)
-/

theorem ex01_id : P → P := by
  intro hP
  exact hP

theorem ex02_imp_trans : (P → Q) → (Q → R) → P → R := by
  intro hPQ hQR hP
  apply hQR
  apply hPQ
  exact hP

theorem ex03_and_comm : P ∧ Q → Q ∧ P := by
  intro hPQ
  constructor
  · exact hPQ.right
  · exact hPQ.left

theorem ex04_or_comm : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP =>
      right
      exact hP
  | inr hQ =>
      left
      exact hQ

theorem ex05_false_elim : False → P := by
  intro hFalse
  exact False.elim hFalse

theorem ex06_double_neg_intro : P → ¬¬P := by
  intro hP hNotP
  apply hNotP
  exact hP

theorem ex07_rw_chain (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  exact h2

theorem ex08_rw_function (h : a = b) : Nat.succ a = Nat.succ b := by
  rw [h]

/-!
## Exercises (Basic Tactics)

Keep proofs small and explicit. Prefer `intro`, `apply`, `exact`, and `rw`.
-/

theorem exercise01 (h : (P ∧ Q) ∧ R) : P ∧ (Q ∧ R) := by
  -- Hint: `constructor` and use projections like `h.left.left`.
  sorry

theorem exercise02 (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  -- Hint: `cases h.right with ...`.
  sorry

theorem exercise03 (hPR : P → R) (hQR : Q → R) : P ∨ Q → R := by
  -- Hint: `intro h`; then `cases h` and `apply` the right implication.
  sorry

theorem exercise04 : (P ↔ Q) → (Q ↔ P) := by
  -- Hint: `intro h`; `constructor`; use `h.mp` and `h.mpr`.
  sorry

theorem exercise05 : ¬ (P ∧ ¬ P) := by
  -- Hint: `intro h`; then `apply h.right`; `exact h.left`.
  sorry

theorem exercise06 (h1 : a = b) (h2 : b = c) :
    Nat.succ (Nat.succ a) = Nat.succ (Nat.succ c) := by
  -- Hint: use `rw [h1, h2]`.
  sorry

end PropositionalLogic

end LogicWorld2
end LeanRwDist
