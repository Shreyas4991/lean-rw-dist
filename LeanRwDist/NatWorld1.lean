import Mathlib

/-!
# Nat World 1: Building and Reasoning About `OurNat`

In this file we define our own natural numbers and practice core proof tactics.
-/

set_option autoImplicit false

namespace LeanRwDist
namespace NatWorld1

/-- Our own natural numbers: either `zero` or `succ n`. -/
inductive OurNat where
  | zero : OurNat
  | succ : OurNat → OurNat
deriving DecidableEq, Repr

namespace OurNat

/-- Addition by recursion on the first argument. -/
def add : OurNat → OurNat → OurNat
  | zero, n => n
  | succ m, n => succ (add m n)

/-- Detect whether a number is zero. -/
def isZero : OurNat → Bool
  | zero => true
  | succ _ => false

/-- Bump zero to one, otherwise keep the input unchanged. -/
def bumpIfZero (n : OurNat) : OurNat :=
  if n = zero then succ zero else n

/-!
## Lean-Generated Equational Facts

For recursive definitions, Lean computes by unfolding equations.
These goals close by `rfl`.
-/

example (n : OurNat) : add zero n = n := rfl
example (m n : OurNat) : add (succ m) n = succ (add m n) := rfl
example : isZero zero = true := rfl
example (n : OurNat) : isZero (succ n) = false := rfl

/-!
## Worked Examples
-/

-- `cases`: every `OurNat` is either `zero` or `succ k`.
theorem ex01_cases_shape (n : OurNat) : n = zero ∨ ∃ k, n = succ k := by
  cases n with
  | zero =>
      left
      rfl
  | succ k =>
      right
      exact ⟨k, rfl⟩

-- Another `cases` proof: if `isZero n = true`, then `n` must be `zero`.
theorem ex02_cases_isZero (n : OurNat) (h : isZero n = true) : n = zero := by
  cases n with
  | zero =>
      rfl
  | succ k =>
      -- Here `h` becomes `false = true`, which is impossible.
      cases h

-- `induction`: prove a recursive fact (`n + 0 = n`).
theorem ex03_induction_add_zero_right (n : OurNat) : add n zero = n := by
  induction n with
  | zero =>
      rfl
  | succ k ih =>
      change succ (add k zero) = succ k
      exact congrArg succ ih

-- Another `induction` proof: `n + (succ m) = succ (n + m)`.
theorem ex04_induction_add_succ_right (n m : OurNat) :
    add n (succ m) = succ (add n m) := by
  induction n with
  | zero =>
      rfl
  | succ k ih =>
      change succ (add k (succ m)) = succ (succ (add k m))
      exact congrArg succ ih

-- `split_ifs`: branch on an `if` condition inside the goal.
theorem ex05_split_ifs (n : OurNat) :
    bumpIfZero n = n ∨ bumpIfZero n = succ zero := by
  unfold bumpIfZero
  split_ifs with hZero
  · right
    rfl
  · left
    rfl

-- `injection`: constructors are injective.
theorem ex06_injection {m n : OurNat} (h : succ m = succ n) : m = n := by
  injection h with hmn

/-!
## Exercises

Keep these elementary and use the named tactic in each hint.
-/

theorem exercise01 (n : OurNat) : isZero (succ n) = false := by
  sorry

theorem exercise02 (n : OurNat) : n = zero ∨ ∃ k, n = succ k := by
  sorry

theorem exercise03 (n : OurNat) : add n zero = n := by
  sorry

theorem exercise04 (n m : OurNat) : add n (succ m) = succ (add n m) := by
  sorry

theorem exercise05 (n : OurNat) :
    bumpIfZero n = n ∨ bumpIfZero n = succ zero := by
  -- Hint: `unfold bumpIfZero` and then `split_ifs`.
  sorry

theorem exercise06 {m n : OurNat} (h : succ m = succ n) : m = n := by
  -- Hint: use `injection h`.
  sorry

end OurNat
end NatWorld1
end LeanRwDist
