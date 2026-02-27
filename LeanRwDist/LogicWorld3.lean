import Mathlib

/-!
# Logic World 3: Powerful Automation

Same theorem statements as `LogicWorld1` and `LogicWorld2`,
now with tactics like `simp`, `aesop`, and `grind`.
-/

set_option autoImplicit false

namespace LeanRwDist
namespace LogicWorld3

section PropositionalLogic

variable (P Q R : Prop)
variable (a b c : Nat)

/-!
## Worked Examples (Automation)
-/

theorem ex01_id : P → P := by
  aesop

theorem ex02_imp_trans : (P → Q) → (Q → R) → P → R := by
  aesop

theorem ex03_and_comm : P ∧ Q → Q ∧ P := by
  aesop

theorem ex04_or_comm : P ∨ Q → Q ∨ P := by
  aesop

theorem ex05_false_elim : False → P := by
  aesop

theorem ex06_double_neg_intro : P → ¬¬P := by
  aesop

theorem ex07_rw_chain (h1 : a = b) (h2 : b = c) : a = c := by
  grind

theorem ex08_rw_function (h : a = b) : Nat.succ a = Nat.succ b := by
  simp [h]

/-!
## Exercises (Automation)

Try solving these with short scripts using `simp`, `aesop`, or `grind`.
-/

theorem exercise01 (h : (P ∧ Q) ∧ R) : P ∧ (Q ∧ R) := by
  -- Hint: `aesop` can usually solve this directly.
  sorry

theorem exercise02 (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  -- Hint: first try `aesop`; if needed, split manually then `aesop`.
  sorry

theorem exercise03 (hPR : P → R) (hQR : Q → R) : P ∨ Q → R := by
  -- Hint: this is a classic `aesop` goal.
  sorry

theorem exercise04 : (P ↔ Q) → (Q ↔ P) := by
  -- Hint: `aesop` or `simp` both work.
  sorry

theorem exercise05 : ¬ (P ∧ ¬ P) := by
  -- Hint: `aesop` should close this from contradiction.
  sorry

theorem exercise06 (h1 : a = b) (h2 : b = c) :
    Nat.succ (Nat.succ a) = Nat.succ (Nat.succ c) := by
  -- Hint: try `grind` or `simp [h1, h2]`.
  sorry

end PropositionalLogic

end LogicWorld3
end LeanRwDist
