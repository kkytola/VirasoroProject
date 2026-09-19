/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib

/-!
# Central charge calculations for Sugawara constructions

Closed forms for the sums of `x`, `x²`, and general quadratic polynomials over an integer
interval `Finset.Ico a b`, with values cast into a field of characteristic zero.


All three lemmas hold for any `a b : ℤ` with `a ≤ b`, so they cover both sign regimes
(`0 ≤ n` and `n ≤ 0`) of the central-charge computation without any reflection tricks.

## Main statements

* `sum_Ico_quadratic`: `∑ x ∈ Finset.Ico a b, (c₂ x² + c₁ x + c₀)` in closed form.
* `bosonic_sugawara_cc_calc_nonneg`: For any `n ∈ ℕ`, we have
  `∑ l (0 ≤ l < n), (l : ℚ) * (n - l) = (n^3 - n) / 6`.

## Tags

central charge, Sugawara construction, Gauss sum

-/

namespace VirasoroProject

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Gauss sum over an integer interval `∑_{x=a}^{b-1} x = (a+b-1)(b-a)/2`, cast into a field of
characteristic zero. -/
lemma sum_Ico_id (a b : ℤ) (hab : a ≤ b) :
    ∑ x ∈ Finset.Ico a b, (x : 𝕜) = ((a : 𝕜) + b - 1) * ((b : 𝕜) - a) / 2 := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hb ih =>
    have hins : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega), ih]
    push_cast; ring

/-- Sum of squares over an integer interval
`∑_{x=a}^{b-1} x² = (b-1)b(2b-1)/6 - (a-1)a(2a-1)/6`, cast into a field of characteristic
zero. -/
lemma sum_Ico_sq (a b : ℤ) (hab : a ≤ b) :
    ∑ x ∈ Finset.Ico a b, (x : 𝕜) ^ 2
      = ((b : 𝕜) - 1) * (b : 𝕜) * (2 * (b : 𝕜) - 1) / 6
        - ((a : 𝕜) - 1) * (a : 𝕜) * (2 * (a : 𝕜) - 1) / 6 := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hb ih =>
    have hins : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega), ih]
    push_cast; ring

/-- Closed form for the sum of a quadratic polynomial `c₂ x² + c₁ x + c₀` over an integer
interval `Finset.Ico a b`, cast into a field of characteristic zero. -/
lemma sum_Ico_quadratic (a b : ℤ) (hab : a ≤ b) (c₂ c₁ c₀ : 𝕜) :
    ∑ x ∈ Finset.Ico a b, (c₂ * (x : 𝕜) ^ 2 + c₁ * (x : 𝕜) + c₀)
      = c₂ * (((b : 𝕜) - 1) * (b : 𝕜) * (2 * (b : 𝕜) - 1) / 6
              - ((a : 𝕜) - 1) * (a : 𝕜) * (2 * (a : 𝕜) - 1) / 6)
        + c₁ * (((a : 𝕜) + b - 1) * ((b : 𝕜) - a) / 2)
        + c₀ * ((b : 𝕜) - a) := by
  have hcard : ((Finset.Ico a b).card : 𝕜) = (b : 𝕜) - a := by
    rw [Int.card_Ico]
    exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ b - a)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hcard, sum_Ico_id a b hab, sum_Ico_sq a b hab]
  ring

/-- The Gauss sum `∑_{l=0}^{n-1} l = (n² - n) / 2` for `n ∈ ℕ`, evaluated in `ℚ`. -/
private lemma sum_range_id_cast (n : ℕ) :
    ∑ l ∈ Finset.range n, (l : ℚ) = ((n : ℚ) ^ 2 - n) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The elementary sum `∑_{l=0}^{n-1} l (n - l) = (n³ - n) / 6` for `n ∈ ℕ`, evaluated in `ℚ`.

(This form of the central charge computation of the basic bosonic Sugawara construction is
referenced in the blueprint; the Lean proof of `VirasoroProject.commutator_sugawaraGen` uses
the more general `VirasoroProject.sum_Ico_quadratic` directly.) -/
lemma bosonic_sugawara_cc_calc_nonneg (n : ℕ) :
    ∑ l ∈ Finset.range n, (l : ℚ) * (n - l) = (n ^ 3 - n) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have expand : ∀ l ∈ Finset.range n, (l : ℚ) * ((n + 1 : ℕ) - l) = (l : ℚ) * (n - l) + l := by
      intro l _; push_cast; ring
    calc  ∑ l ∈ Finset.range (n + 1), (l : ℚ) * ((n + 1 : ℕ) - l)
      -- Split off the top term `l = n`, which contributes `n · 1`.
      _ = (∑ l ∈ Finset.range n, (l : ℚ) * ((n + 1 : ℕ) - l)) + n := by
          rw [Finset.sum_range_succ]; push_cast; ring
      -- In the remaining sum, `l ((n+1) - l) = l (n - l) + l`.
      _ = ((∑ l ∈ Finset.range n, (l : ℚ) * (n - l)) + ∑ l ∈ Finset.range n, (l : ℚ)) + n := by
          rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib]
      _ = ((n + 1 : ℕ) ^ 3 - (n + 1 : ℕ)) / 6 := by
          rw [ih, sum_range_id_cast]; push_cast; ring

end VirasoroProject
