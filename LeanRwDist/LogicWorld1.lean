import Mathlib

/-!
# Logic World 1: Propositions as Types (Term Mode)

In this world, proofs are plain terms.
Read each theorem as "build a value of this type".
-/

set_option autoImplicit false

namespace LeanRwDist
namespace LogicWorld1

section PropositionalLogic

variable (P Q R : Prop)
variable (a b c : Nat)

/-!
## Worked Examples (Term Mode)
-/

-- A proof of `P → P` is just a function that returns its input proof.
theorem ex01_id : P → P :=
  fun hP => hP

-- Function composition at the level of proofs.
theorem ex02_imp_trans : (P → Q) → (Q → R) → P → R :=
  fun hPQ hQR hP => hQR (hPQ hP)

-- `∧` is a pair of proofs, so we can swap fields.
theorem ex03_and_comm : P ∧ Q → Q ∧ P :=
  fun hPQ => And.intro hPQ.right hPQ.left

-- `∨` is a tagged union, so we eliminate by cases.
theorem ex04_or_comm : P ∨ Q → Q ∨ P :=
  fun h =>
    Or.elim h
      (fun hP => Or.inr hP)
      (fun hQ => Or.inl hQ)

-- From `False`, anything follows.
theorem ex05_false_elim : False → P :=
  fun hFalse => False.elim hFalse

-- If you have `P`, then "not not P" is immediate.
theorem ex06_double_neg_intro : P → ¬¬P :=
  fun hP hNotP => hNotP hP

-- Equality can be chained transitively.
theorem ex07_rw_chain (h1 : a = b) (h2 : b = c) : a = c :=
  Eq.trans h1 h2

-- Equality can be mapped through functions with `congrArg`.
theorem ex08_rw_function (h : a = b) : Nat.succ a = Nat.succ b :=
  congrArg Nat.succ h

/-!
## Exercises (Term Mode)

Replace each `sorry` with a term proof.
Try to avoid tactic scripts in this file.
-/

theorem exercise01 (h : (P ∧ Q) ∧ R) : P ∧ (Q ∧ R) := by
  -- Hint: use `h.left.left`, `h.left.right`, and `h.right`.
  sorry

theorem exercise02 (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  -- Hint: split on `h.right` with `Or.elim`.
  sorry

theorem exercise03 (hPR : P → R) (hQR : Q → R) : P ∨ Q → R := by
  -- Hint: this is case analysis on `P ∨ Q`.
  sorry

theorem exercise04 : (P ↔ Q) → (Q ↔ P) := by
  -- Hint: build a proof with `Iff.intro`.
  sorry

theorem exercise05 : ¬ (P ∧ ¬ P) := by
  -- Hint: if `h : P ∧ ¬ P`, apply `h.right` to `h.left`.
  sorry

theorem exercise06 (h1 : a = b) (h2 : b = c) :
    Nat.succ (Nat.succ a) = Nat.succ (Nat.succ c) := by
  -- Hint: combine `Eq.trans` and `congrArg`.
  sorry

end PropositionalLogic

end LogicWorld1
end LeanRwDist
