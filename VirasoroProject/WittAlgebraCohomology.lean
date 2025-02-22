/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import VirasoroProject.VirasoroCocycle

/-!
# The 2-cohomology of the Witt algebra is generated by the Virasoro cocycle

In this file it is proven that the 2-cohomology of the Witt algebra with scalar coefficients
is one-dimensional, and generated by the Virasoro cocycle.

## Main statements

* `WittAlgebra.exists_add_bdry_eq_smul_virasoroCocycle`: Any Witt algebra 2-cocycle
  can be modified by a coboundary to make it proportional to the Virasoro cocycle.
* `WittAlgebra.rank_lieTwoCohomology_eq_one`: This is (the result of) the calculation of the
  dimension of the 2-cohomology of the Witt algebra, dim H²(WittAlgebra, 𝕜) = 1.

## Tags

Witt algebra, Lie algebra cohomology

-/

namespace VirasoroProject

namespace WittAlgebra

variable {𝕜 : Type*} [Field 𝕜]
variable [CharZero 𝕜]

variable (γ : LieTwoCocycle 𝕜 (WittAlgebra 𝕜) 𝕜)

/-- A 1-cocycle of the Witt algebra, which is used to make a 2-cocycle proportional to the
Virasoro cocycle by the addition of the corresponding coboundary. -/
noncomputable def normalizingCocycle : LieOneCocycle 𝕜 (WittAlgebra 𝕜) 𝕜 where
  toLinearMap := (WittAlgebra.lgen 𝕜).constr 𝕜 <|
      fun n ↦ if n = 0
        then (-2⁻¹ : 𝕜) • γ (lgen 𝕜 1) (lgen 𝕜 (-1))
        else (1/n : 𝕜) • γ (lgen 𝕜 0) (lgen 𝕜 n)

lemma normalizingCocycle_apply_lgen_zero :
    normalizingCocycle γ (lgen 𝕜 0) = (-2⁻¹ : 𝕜) * γ (lgen 𝕜 1) (lgen 𝕜 (-1)) := by
  have aux := (WittAlgebra.lgen 𝕜).constr_basis 𝕜 (fun n ↦ if n = 0
        then (-2⁻¹ : 𝕜) • γ (lgen 𝕜 1) (lgen 𝕜 (-1))
        else (1/n : 𝕜) • γ (lgen 𝕜 0) (lgen 𝕜 n)) 0
  dsimp at aux
  rw [← aux]
  congr

lemma normalizingCocycle_apply_lgen (n : ℤ) (hn : n ≠ 0) :
    normalizingCocycle γ (lgen 𝕜 n) = (1/n : 𝕜) * γ (lgen 𝕜 0) (lgen 𝕜 n) := by
  have aux := (WittAlgebra.lgen 𝕜).constr_basis 𝕜 (fun n ↦ if n = 0
        then (-2⁻¹ : 𝕜) • γ (lgen 𝕜 1) (lgen 𝕜 (-1))
        else (1/n : 𝕜) • γ (lgen 𝕜 0) (lgen 𝕜 n)) n
  dsimp at aux
  simp only [hn, ↓reduceIte] at aux
  rw [← aux]
  congr

private lemma add_bdry_normalizingCocycle_apply_lgen_one :
    (γ + (normalizingCocycle γ).bdry) (lgen 𝕜 1) (lgen 𝕜 (-1)) = 0 := by
  simp only [Int.reduceNeg, LieTwoCocycle.add_apply, LieOneCocycle.bdry_apply, bracket_lgen_lgen,
    Int.cast_one, Int.cast_neg, sub_neg_eq_add, add_neg_cancel, map_smul,
    normalizingCocycle_apply_lgen_zero, neg_mul, smul_eq_mul, mul_neg]
  ring

private lemma add_bdry_normalizingCocycle_apply_lgen_zero (n : ℤ) (hn : n ≠ 0) :
    (γ + (normalizingCocycle γ).bdry) (lgen 𝕜 0) (lgen 𝕜 n) = 0 := by
  simp only [LieTwoCocycle.add_apply, LieOneCocycle.bdry_apply, bracket_lgen_lgen, Int.cast_zero,
    zero_sub, zero_add, neg_smul, map_neg, map_smul, smul_eq_mul]
  rw [normalizingCocycle_apply_lgen γ n hn]
  simp only [one_div, ← mul_assoc]
  simp [show (n : 𝕜) * (n : 𝕜)⁻¹ = 1 from mul_inv_cancel₀ <| Int.cast_ne_zero.mpr hn]

/-- The 2-cocycle equation in the standard basis `ℓₙ` of the Witt algebra:
    `0 = (m-k) * γ(n,m+k) + (k-n) * γ(m,n+k) + (n-m) * γ(k,n+m)`. -/
private lemma add_lieTwoCocycle_apply_lgen_lgen_lgen_eq_zero (n m k : ℤ) :
    (m - k) * γ (lgen 𝕜 n) (lgen 𝕜 (m + k)) + (k - n) * γ (lgen 𝕜 m) (lgen 𝕜 (n + k))
     + (n - m) * γ (lgen 𝕜 k) (lgen 𝕜 (n + m)) = 0 := by
  have key := γ.leibniz (X := lgen 𝕜 n) (Y := lgen 𝕜 m) (Z := lgen 𝕜 k)
  simp only [bracket_lgen_lgen, map_smul, smul_eq_mul, LinearMap.smul_apply] at key
  simp only [← γ.skew (lgen 𝕜 k), key, sub_mul, mul_neg, neg_sub]
  ring

private lemma lieTwoCocycle_apply_lgen_lgen_eq_zero_of_add_ne_zero {n m : ℤ} (ne_zero : n + m ≠ 0)
    (hγ : γ (lgen 𝕜 0) (lgen 𝕜 (n+m)) = 0) :
    γ (lgen 𝕜 n) (lgen 𝕜 m) = 0 := by
  have key := add_lieTwoCocycle_apply_lgen_lgen_lgen_eq_zero γ n m 0
  simp only [hγ, ← γ.skew (lgen 𝕜 m), Int.cast_zero, mul_neg, neg_mul, sub_zero,
             add_zero, zero_sub, neg_neg, ← add_mul, mul_zero, mul_eq_zero] at key
  simpa [show (m : 𝕜) + n ≠ 0 by rw [add_comm] ; exact_mod_cast ne_zero] using key

lemma exists_add_bdry_eq_smul_virasoroCocycle :
    ∃ (r : 𝕜), γ + (normalizingCocycle γ).bdry = r • virasoroCocycle 𝕜 := by
  set γ₀ := γ + (normalizingCocycle γ).bdry -- notation decluttering
  set r := 2 * γ₀ ((lgen 𝕜) 2) ((lgen 𝕜) (-2)) with hr -- notation decluttering
  use r
  -- By bilinearity, it suffices to check the equality on basis element pairs.
  suffices ∀ (n m : ℤ),
      γ₀ (lgen 𝕜 n) (lgen 𝕜 m) = r * virasoroCocycle 𝕜 (lgen 𝕜 n) (lgen 𝕜 m) by
    apply LieTwoCocycle.ext
    apply (WittAlgebra.lgen 𝕜).ext fun n ↦ ?_
    apply (WittAlgebra.lgen 𝕜).ext fun m ↦ this n m
  intro n m
  by_cases hnm : n + m = 0
  · -- The case n + m = 0 involves the main calculation.
    suffices ∀ (k : ℕ),
        γ₀ ((lgen 𝕜) k) ((lgen 𝕜) (-k : ℤ)) = r * ((k : ℤ)^3 - (k : ℤ)) / 12 by
      simp only [virasoroCocycle_apply_lgen_lgen, hnm, ↓reduceIte]
      by_cases hn : 0 ≤ n
      · specialize this n.toNat
        have n_eq : n.toNat = n := Int.toNat_of_nonneg hn
        simp_rw [n_eq] at this
        simp_rw [show m = -n by linarith, this, mul_div]
      · specialize this m.toNat
        simp only [not_le] at hn
        have m_eq : m.toNat = m := Int.toNat_of_nonneg <| by linarith
        rw [← LieTwoCocycle.skew]
        simp_rw [show n = -m by linarith, m_eq] at hn this ⊢
        rw [this]
        have aux : (-m)^3 = -(m^3) := by
          rw [(pow_eq_neg_pow_iff (by linarith)).mpr ⟨rfl, Nat.odd_iff.mpr rfl⟩]
        simp [show (-m : 𝕜)^3 = -((m : 𝕜)^3) by exact_mod_cast aux]
        ring
    intro k
    induction' k using Nat.strong_induction_on with j hj
    by_cases j_small : j ∈ ({0, 1, 2} : Finset ℕ)
    · fin_cases j_small
      · -- k = 0 case is true for any cocycle by skew-symmetry
        simp
      · -- k = 1 case follows due to the choice of the normalizing coboundary
        convert add_bdry_normalizingCocycle_apply_lgen_one γ
        ring
      · -- k = 2 case is what determines the choice of the multiplicative constant r
        rw [hr]
        norm_num
        ring
    · have j_large : 2 < j := by match j with
        | 0 => contradiction | 1 => contradiction | 2 => contradiction
        | j' + 3 => simp
      -- For j ≥ 3, the coefficient (2-j) in a key recusive equation does not vanish.
      have not_zero : (2 - j : 𝕜) ≠ 0 := by exact_mod_cast show (2 - j : ℤ) ≠ 0 by linarith
      -- The key recursive equation is obtained by taking n = j, m = 1-j, k = -1
      -- in the cocycle condition written in the basis `(ℓₙ)`.
      -- This equation generally simplifies to
      -- `0 = (2-j) * γ(j,-j) + (1+j) * γ(j-1,1-j) + (1-2j) * γ(1,-1)`
      -- but the last term is zero for `γ₀` because of the normalizing coboundary.
      set j' := j - 1 with hj'
      have aux : (j - 1 : ℤ) = j' := (Int.natCast_pred_of_pos (by linarith)).symm
      have aux' : (1 - j : ℤ) = -j' := by simp [← aux]
      have eqn : ((2 - j : 𝕜)) * γ₀ (lgen 𝕜 j) (lgen 𝕜 (-j))
                   + ((1 + j : 𝕜)) * γ₀ (lgen 𝕜 j') (lgen 𝕜 (-j')) = 0 := by
        have eqn := add_lieTwoCocycle_apply_lgen_lgen_lgen_eq_zero γ₀ j (1-j) (-1)
        simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast, Int.reduceNeg, Int.cast_neg,
                  sub_neg_eq_add, add_sub_cancel] at eqn
        rw [← γ₀.skew (lgen 𝕜 (-1)), ← γ₀.skew (lgen 𝕜 (1 - j))] at eqn
        have nothing : -(γ₀ ((lgen 𝕜) 1)) ((lgen 𝕜) (-1)) = 0 := by
          simpa using hj 1 (by linarith)
        simp only [nothing, Int.reduceNeg, mul_neg, mul_zero, add_zero] at eqn
        rw [show (1 : 𝕜) - j + 1 = 2 - j by ring, show (1 : ℤ) - j + -1 = -j by ring] at eqn
        rw [← neg_mul, show (-(1 : 𝕜) - j) = -(1 + j) by ring, neg_neg] at eqn
        rw [hj', ← eqn]
        simp only [Int.reduceNeg, add_right_inj, mul_eq_mul_left_iff, ← aux, aux']
        left
        congr
      rw [hj j' (by linarith), hj'] at eqn
      simp only [Int.cast_natCast] at eqn
      rw [add_eq_zero_iff_eq_neg] at eqn
      have solve := congr_arg (fun (z : 𝕜) ↦ (2 - j : 𝕜)⁻¹ * z) eqn
      simp only [not_zero, isUnit_iff_ne_zero, ne_eq, not_false_eq_true, IsUnit.inv_mul_cancel_left,
                 mul_neg] at solve
      rw [solve, mul_div, mul_div, ← neg_div]
      congr
      calc -((2 - ↑j)⁻¹ * ((1 + ↑j) * (r * (↑(j - 1) ^ 3 - ↑(j - 1)))))
          = -((2 - ↑j)⁻¹ * ((1 + ↑j) * (r * ((↑j - 1) ^ 3 - (↑j - 1))))) := by
            simp [show (↑(j - 1) : 𝕜) = (↑j : 𝕜) - 1 by exact_mod_cast aux.symm]
        _ = r * -((2 - ↑j)⁻¹ * (↑j - 2) * (↑j ^ 3 - ↑j))  := by ring
        _ = r * (↑j ^ 3 - ↑j)                             := by field_simp [not_zero, ← neg_mul]
        _ = _                                             := by simp
  · -- The case n + m ≠ 0 is straightforward by the choice of the normalizing coboundary.
    suffices ((γ + (normalizingCocycle γ).bdry) ((lgen 𝕜) n)) ((lgen 𝕜) m) = 0 by
      simpa [virasoroCocycle_apply_lgen_lgen, hnm]
    apply lieTwoCocycle_apply_lgen_lgen_eq_zero_of_add_ne_zero (γ + (normalizingCocycle γ).bdry) hnm
    exact add_bdry_normalizingCocycle_apply_lgen_zero γ (n + m) hnm

variable (𝕜)

/-- The Lie algebra 2-cohomology of the Witt algebra is one-dimensional,
`dim H²(WittAlgebra, 𝕜) = 1`. -/
theorem rank_lieTwoCohomology_eq_one :
    Module.rank 𝕜 (LieTwoCohomology 𝕜 (WittAlgebra 𝕜) 𝕜) = 1 := by
  apply Module.rank_eq_one_iff_finrank_eq_one.mpr
  apply finrank_eq_one_iff'.mpr
  use (virasoroCocycle 𝕜).cohomologyClass
  constructor
  · exact cohomologyClass_virasoroCocycle_ne_zero 𝕜
  · intro γ'
    obtain ⟨γ, hγ'⟩ := Quotient.exists_rep γ'
    obtain ⟨r, hr⟩ := exists_add_bdry_eq_smul_virasoroCocycle γ
    use r
    convert (LinearMap.congr_arg (f := LieTwoCocycle.toLieTwoCohomology 𝕜 ..) hr).symm
    rw [← hγ']
    exact (LieTwoCocycle.cohomologyClass_add_bdry γ (normalizingCocycle γ)).symm

end WittAlgebra -- namespace

end VirasoroProject -- namespace
