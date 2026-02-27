import Mathlib

/-!
# Z World 1: Unique Factorization for Integers (Step by Step)

This development avoids using the one-shot integer UFD theorem directly.
Instead, we:
1. reduce integer factorizations to factorizations of absolute values in `ℕ`,
2. use `Nat.primeFactorsList_unique`,
3. pull the result back to integers.

Uniqueness is stated in the standard integer way:
factorizations are unique up to order and sign.
Technically, we encode sign ambiguity by comparing `natAbs` lists.
-/

set_option autoImplicit false

namespace LeanRwDist
namespace ZWorld1

open List

/-!
## Step 1: Basic Integer Facts
-/

/-- The only units in `ℤ` are `1` and `-1`. -/
theorem unit_eq_one_or_neg_one (u : Units ℤ) : (u : ℤ) = 1 ∨ (u : ℤ) = -1 := by
  rcases Int.units_eq_one_or u with h | h
  · left
    simp [h]
  · right
    simp [h]

/-- `Associated` in `ℤ` is equivalent to equal absolute values. -/
theorem associated_iff_natAbs_eq (a b : ℤ) : Associated a b ↔ a.natAbs = b.natAbs := by
  exact (Int.natAbs_eq_iff_associated).symm

/-!
## Step 2: Move a Product in `ℤ` to a Product in `ℕ`
-/

/-- Absolute value of an integer list product is product of absolute values. -/
theorem natAbs_list_prod (l : List ℤ) : (l.map Int.natAbs).prod = (l.prod).natAbs := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      simp [ih, Int.natAbs_mul]

/-- If every integer in `l` is prime, then every `natAbs` in `l.map Int.natAbs` is prime in `ℕ`. -/
theorem nat_prime_of_int_prime_list (l : List ℤ) (h : ∀ p ∈ l, Prime p) :
    ∀ n ∈ l.map Int.natAbs, Nat.Prime n := by
  intro n hn
  rcases List.mem_map.1 hn with ⟨p, hp_mem, hp_eq⟩
  subst hp_eq
  exact (Int.prime_iff_natAbs_prime).mp (h p hp_mem)

/-!
## Step 3: Canonical Uniqueness Target in `ℕ`

If `l` is a prime factorization of `z : ℤ`, then `l.map Int.natAbs` must be
a permutation of `Nat.primeFactorsList z.natAbs`.
-/

theorem perm_natAbs_primeFactorsList_of_factorization
    (z : ℤ) (l : List ℤ)
    (hprime : ∀ p ∈ l, Prime p)
    (hassoc : Associated l.prod z) :
    l.map Int.natAbs ~ Nat.primeFactorsList z.natAbs := by
  have hprodAbs : (l.map Int.natAbs).prod = z.natAbs := by
    calc
      (l.map Int.natAbs).prod = (l.prod).natAbs := natAbs_list_prod l
      _ = z.natAbs := (Int.natAbs_eq_iff_associated).2 hassoc
  exact Nat.primeFactorsList_unique hprodAbs (nat_prime_of_int_prime_list l hprime)

/-!
## Step 4: Build a Canonical Integer Prime Factorization
-/

/-- Canonical factor list for `z : ℤ`: cast nat prime factors of `z.natAbs` to integers. -/
def canonicalIntPrimeFactors (z : ℤ) : List ℤ :=
  z.natAbs.primeFactorsList.map (fun p : ℕ => (p : ℤ))

/-- Every element in the canonical integer factor list is prime in `ℤ`. -/
theorem canonicalIntPrimeFactors_prime (z : ℤ) :
    ∀ p ∈ canonicalIntPrimeFactors z, Prime p := by
  intro p hp
  rcases List.mem_map.1 hp with ⟨n, hn, hnp⟩
  have hp' : p = (n : ℤ) := hnp.symm
  subst hp'
  exact (Nat.prime_iff_prime_int).1 (Nat.prime_of_mem_primeFactorsList hn)

/-- Product of the canonical list is associated to `z`. -/
theorem canonicalIntPrimeFactors_prod_assoc (z : ℤ) (hz : z ≠ 0) :
    Associated (canonicalIntPrimeFactors z).prod z := by
  have hzabs : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hprodNat : (z.natAbs.primeFactorsList).prod = z.natAbs := Nat.prod_primeFactorsList hzabs
  have hprodInt : (canonicalIntPrimeFactors z).prod = (z.natAbs : ℤ) := by
    calc
      (canonicalIntPrimeFactors z).prod
          = (z.natAbs.primeFactorsList.map (fun p : ℕ => (p : ℤ))).prod := rfl
      _ = ((z.natAbs.primeFactorsList).prod : ℤ) := by
          simp [Nat.cast_list_prod]
      _ = (z.natAbs : ℤ) := by
          simp [hprodNat]
  exact hprodInt.symm ▸ (Int.associated_natAbs z).symm

/-!
## Step 5: Final Theorem (Existence + Uniqueness)

For nonzero `z : ℤ`, there exists a list of integer primes multiplying to `z` up to a unit.
Any other such list has the same absolute-value factors up to permutation.
-/

theorem integer_unique_factorization (z : ℤ) (hz : z ≠ 0) :
    ∃ l : List ℤ,
      (∀ p ∈ l, Prime p) ∧
      Associated l.prod z ∧
      (∀ l' : List ℤ,
        (∀ p ∈ l', Prime p) →
        Associated l'.prod z →
        l'.map Int.natAbs ~ l.map Int.natAbs) := by
  refine ⟨canonicalIntPrimeFactors z, canonicalIntPrimeFactors_prime z,
    canonicalIntPrimeFactors_prod_assoc z hz, ?_⟩
  intro l' hl' hprod'
  have hcanon :
      (canonicalIntPrimeFactors z).map Int.natAbs ~ Nat.primeFactorsList z.natAbs := by
    exact perm_natAbs_primeFactorsList_of_factorization z (canonicalIntPrimeFactors z)
      (canonicalIntPrimeFactors_prime z) (canonicalIntPrimeFactors_prod_assoc z hz)
  have hother : l'.map Int.natAbs ~ Nat.primeFactorsList z.natAbs := by
    exact perm_natAbs_primeFactorsList_of_factorization z l' hl' hprod'
  exact hother.trans hcanon.symm

end ZWorld1
end LeanRwDist
