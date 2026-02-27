import Mathlib

/-!
# Nat World 2: Lean Naturals + Mathlib

In this world we use Lean's built-in type `Nat`.
So we can rely on standard notation (`+`, `*`, `≤`, ...) and a large theorem library.
-/

set_option autoImplicit false

namespace LeanRwDist
namespace NatWorld2

section NatArithmetic

/-!
## A Small Euclid Step

`euclidStep a b` does one step of Euclid's algorithm:
- if `a = 0`, stop with `(0, b)`
- otherwise move to `(b % a, a)`
-/

def euclidStep (a b : ℕ) : ℕ × ℕ :=
  if a = 0 then (0, b) else (b % a, a)

/-!
## Worked Examples
-/

-- Warm-up: `Nat.add_zero` is already in the library.
theorem ex01_add_zero (n : ℕ) : n + 0 = n := by
  exact Nat.add_zero n

-- Warm-up: reorder terms with associativity + commutativity.
theorem ex02_add_swap (a b c : ℕ) : a + b + c = a + c + b := by
  calc
    a + b + c = a + (b + c) := by rw [Nat.add_assoc]
    _ = a + (c + b) := by rw [Nat.add_comm b c]
    _ = a + c + b := by rw [Nat.add_assoc]

-- Library theorem for one Euclid recursion step.
theorem ex03_gcd_rec (a b : ℕ) : Nat.gcd a b = Nat.gcd (b % a) a := by
  exact Nat.gcd_rec a b

-- The same step in the "standard textbook" shape.
theorem ex04_gcd_euclid_step (a b : ℕ) : Nat.gcd a b = Nat.gcd b (a % b) := by
  calc
    Nat.gcd a b = Nat.gcd b a := by rw [Nat.gcd_comm]
    _ = Nat.gcd (a % b) b := by exact Nat.gcd_rec b a
    _ = Nat.gcd b (a % b) := by rw [Nat.gcd_comm]

-- One-step algorithm invariance: gcd of the pair does not change.
theorem ex05_euclidStep_invariant (a b : ℕ) :
    Nat.gcd (euclidStep a b).1 (euclidStep a b).2 = Nat.gcd a b := by
  by_cases h : a = 0
  · subst h
    simp [euclidStep]
  · have hstep : Nat.gcd (b % a) a = Nat.gcd a b := by
      exact (Nat.gcd_rec a b).symm
    simpa [euclidStep, h] using hstep

-- `gcd a b` divides each input.
theorem ex06_gcd_dvd_both (a b : ℕ) : Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b := by
  constructor
  · exact Nat.gcd_dvd_left a b
  · exact Nat.gcd_dvd_right a b

-- If `d` divides both numbers, then `d` divides their gcd.
theorem ex07_dvd_gcd {d a b : ℕ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ Nat.gcd a b := by
  exact Nat.dvd_gcd ha hb

-- Coprimality is preserved by one Euclid reduction step.
theorem ex08_coprime_euclid_step (a b : ℕ) :
    Nat.Coprime a b ↔ Nat.Coprime b (a % b) := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, ex04_gcd_euclid_step]

/-!
## Exercises

These are intentionally a bit harder than NatWorld1.
Use library lemmas (`Nat.gcd_rec`, `Nat.dvd_gcd`, etc.) aggressively.
-/

theorem exercise01 (a b : ℕ) : Nat.gcd a b = Nat.gcd (b % a) a := by
  -- Hint: this is exactly `Nat.gcd_rec a b`.
  sorry

theorem exercise02 (a b : ℕ) : Nat.gcd a b = Nat.gcd b (a % b) := by
  -- Hint: combine `Nat.gcd_comm` and `Nat.gcd_rec`.
  sorry

theorem exercise03 (a b k : ℕ) : Nat.gcd a b ∣ a + k * b := by
  -- Hint: `gcd a b ∣ a` and `gcd a b ∣ b`; then use `dvd_mul_of_dvd_right` and `dvd_add`.
  sorry

theorem exercise04 {d a b : ℕ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ Nat.gcd a b := by
  -- Hint: this is exactly `Nat.dvd_gcd ha hb`.
  sorry

theorem exercise05 (a b : ℕ) : Nat.Coprime a b ↔ Nat.Coprime b (a % b) := by
  -- Hint: rewrite both sides using `Nat.coprime_iff_gcd_eq_one`.
  sorry

theorem exercise06 (a b : ℕ) :
    Nat.gcd (euclidStep a b).1 (euclidStep a b).2 = Nat.gcd a b := by
  -- Hint: split by `by_cases h : a = 0`; use `simp [euclidStep, h]` and `Nat.gcd_rec`.
  sorry

end NatArithmetic

end NatWorld2
end LeanRwDist
