/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import VirasoroProject.VirasoroAlgebra
import VirasoroProject.HeisenbergAlgebra
import VirasoroProject.CentralChargeCalc
import VirasoroProject.Commutator
import VirasoroProject.LieAlgebraRepresentationOfBasis
import VirasoroProject.ToMathlib.Topology.Algebra.Module.LinearMap.Defs
import Mathlib

/-!
# The bosonic Sugawara construction

This file contains the basic bosonic Sugawara construction.

## Main definitions

* `VirasoroAlgebra.representationOfCentralChargeOfL`: A variant of the construction
  (`LieAlgebra.representationOfBasis`) of a representation of a Lie algebra from operators
  corresponding to a basis, for the special case of the Virasoro algebra: a representation is
  constructed from operators corresponding to the `lgen` Virasoro generators satisfying
  commutation relations with a given central charge `c`.
* `VirasoroProject.sugawaraRepresentation`: Any representation of the Heisenberg algebra
  where the Heisenberg modes act in a locally truncated fashion can be made into a representation
  of the Virasoro algebra with central charge `c = 1` by the (basic) bosonic Sugawara construction.

## Main statements

* `VirasoroProject.commutator_sugawaraGen`: Given operators `A(k)`, `k ∈ ℤ`, satisfying Heisengerg
  algebra commutation relations and acting in a locally truncated way, the Sugawara operators
  `Lₙ = 1/2 • ∑ k, :A(n-k)A(k):` for `n ∈ ℤ` satisfy the commutation relations of the Virasoro
  generators (here the normal ordered product `:A(n-k)A(k):` is the composition of `A(n-k)` and
  `A(k)` in an order depending on the indices `n-k` and `k`).
* `VirasoroProject.sugawaraRepresentation_lgen_apply`: In `VirasoroProject.sugawaraRepresentation`,
  the Virasoro generators `lgen _ n`, `n ∈ ℤ`, act by the Sugawara formula
  `Lₙ = 1/2 • ∑ k ≥ 0, A(n-k) ∘ A(k) + 1/2 • ∑ k < 0, A(k) ∘ A(n-k)`.
* `VirasoroProject.sugawaraRepresentation_cgen_apply`: In `VirasoroProject.sugawaraRepresentation`,
  the central charge is `c = 1`, i.e., the Virasoro generator `cgen _` acts as `1 • id`.

## Tags

Sugawara construction, Virasoro algebra, Heisenberg algebra, bosonic Fock space

-/

namespace VirasoroProject



section Sugawara_boson

open Filter

variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

variable (heiOper : ℤ → (V →ₗ[𝕜] V))
variable (heiTrunc : ∀ v, atTop.Eventually (fun l ↦ (heiOper l) v = 0))
variable (heiComm : ∀ k l,
  (heiOper k).commutator (heiOper l) = if k + l = 0 then (k : 𝕜) • 1 else 0)

section normal_ordered_pair

/-- Normal ordered pair of two operators:
`pairNO k l` equals `(heiOper l) ∘ (heiOper k)` if `l ≤ k`,
and `(heiOper k) ∘ (heiOper l)` otherwise. -/
def pairNO (k l : ℤ) : (V →ₗ[𝕜] V) :=
  if l ≤ k then ((heiOper l) ∘ₗ (heiOper k)) else ((heiOper k) ∘ₗ (heiOper l))

/-- Alternative normal ordered pair of two operators:
`pairNO' k l` equals `(heiOper l) ∘ (heiOper k)` if `k ≥ 0`,
and `(heiOper k) ∘ (heiOper l)` otherwise. -/
def pairNO' (k l : ℤ) : (V →ₗ[𝕜] V) :=
  if 0 ≤ k then ((heiOper l) ∘ₗ (heiOper k)) else ((heiOper k) ∘ₗ (heiOper l))

lemma pairNO_apply_eq_zero (A : ℤ → (V →ₗ[𝕜] V)) {v : V} {N : ℤ}
    (A_trunc : ∀ n ≥ N, A n v = 0) {k l : ℤ} (h : N ≤ max k l) :
    (pairNO A k l) v = 0 := by
  cases' le_sup_iff.mp h with k_large l_large
  · by_cases hlk : l ≤ k
    · simp [pairNO, hlk, A_trunc k k_large]
    · simp [pairNO, hlk, A_trunc l (by linarith)]
  · by_cases hlk : l ≤ k
    · simp [pairNO, hlk, A_trunc k (by linarith)]
    · simp [pairNO, hlk, A_trunc l l_large]

include heiComm

/-- `heiOper k` and `heiOper l` commute unless `k = l`. -/
lemma heiComm_of_add_ne_zero {k l : ℤ} (hkl : k + l ≠ 0) :
    (heiOper k) ∘ₗ (heiOper l) = (heiOper l) ∘ₗ (heiOper k) := by
  simpa [hkl, sub_eq_zero, LinearMap.commutator] using heiComm k l

variable {heiOper}

/-- The two definitions of normal ordered pairs coincide. -/
lemma heiOper_pairNO_eq_pairNO' (k l : ℤ) :
    pairNO heiOper k l = pairNO' heiOper k l := by
  unfold pairNO pairNO'
  by_cases hk : 0 ≤ k
  · simp only [hk, ↓reduceIte, ite_eq_left_iff, not_le]
    intro hkl
    apply heiComm_of_add_ne_zero _ heiComm
    linarith
  · simp only [hk, ↓reduceIte, ite_eq_right_iff]
    intro hlk
    apply heiComm_of_add_ne_zero _ heiComm
    linarith

include heiTrunc in
omit heiComm in
lemma finite_support_smul_pairNO_heiOper_apply {𝕂 : Type*} [SMulZeroClass 𝕂 V]
    (n m : ℤ) (a : ℤ → 𝕂) (v : V) :
    (Function.support fun k ↦ a k • ((pairNO heiOper (m - k) (n + k)) v)).Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp <| heiTrunc v
  apply (Set.finite_Ioo (m - N) (N - n)).subset
  simp only [Function.support_subset_iff, ne_eq]
  intro k hk
  by_contra con
  apply hk
  rw [pairNO_apply_eq_zero heiOper hN ?_, smul_zero]
  by_cases h : N ≤ n + k
  · exact le_sup_of_le_right h
  · apply le_sup_of_le_left
    simp only [Set.mem_Ioo, not_and, not_lt, tsub_le_iff_right] at con
    by_contra con'
    linarith [con (by linarith)]

include heiTrunc in
omit heiComm in
lemma finite_support_pairNO_heiOper_apply (n m : ℤ) (v : V) :
    (Function.support fun k ↦ ((pairNO heiOper (m - k) (n + k)) v)).Finite := by
  apply (finite_support_smul_pairNO_heiOper_apply heiTrunc n m  (fun _ ↦ 1) v).subset
  intro k hk
  simp only [Function.mem_support, ne_eq, one_smul] at hk ⊢
  grind

include heiTrunc in
lemma finite_support_smul_pairNO'_heiOper_apply {𝕂 : Type*} [SMulZeroClass 𝕂 V]
    (n m : ℤ) (a : ℤ → 𝕂) (v : V) :
    (Function.support fun k ↦ a k • ((pairNO' heiOper (m - k) (n + k)) v)).Finite := by
  apply (finite_support_smul_pairNO_heiOper_apply heiTrunc n m a v).subset
  intro j hj
  convert hj using 2
  simp_rw [heiOper_pairNO_eq_pairNO' heiComm]

include heiTrunc in
omit heiComm in
lemma finite_support_smul_pairNO_heiOper_apply₀ {𝕂 : Type*} [SMulZeroClass 𝕂 V]
    (s : ℤ) (a : ℤ → 𝕂) (v : V) :
    (Function.support fun k ↦ (a k • (pairNO heiOper (s - k) k) v)).Finite := by
  simpa using finite_support_smul_pairNO_heiOper_apply heiTrunc 0 s a v

include heiTrunc in
omit heiComm in
lemma finite_support_pairNO_heiOper_apply₀ (s : ℤ) (v : V) :
    (Function.support fun k ↦ ((pairNO heiOper (s - k) k) v)).Finite := by
  simpa using finite_support_pairNO_heiOper_apply heiTrunc 0 s v

include heiTrunc in
lemma finite_support_pairNO'_heiOper_apply (n m : ℤ) (v : V) :
    (Function.support fun k ↦ ((pairNO' heiOper (m - k) (n + k)) v)).Finite := by
  apply (finite_support_pairNO_heiOper_apply heiTrunc n m v).subset
  intro j hj
  convert hj using 2
  simp_rw [heiOper_pairNO_eq_pairNO' heiComm]

include heiTrunc in
lemma finite_support_smul_pairNO'_heiOper_apply₀ {𝕂 : Type*} [SMulZeroClass 𝕂 V]
    (s : ℤ) (a : ℤ → 𝕂) (v : V) :
    (Function.support fun k ↦ (a k • (pairNO' heiOper (s - k) k) v)).Finite := by
  simpa using finite_support_smul_pairNO'_heiOper_apply heiTrunc heiComm 0 s a v

include heiTrunc in
lemma finite_support_pairNO'_heiOper_apply₀ (s : ℤ) (v : V) :
    (Function.support fun k ↦ ((pairNO' heiOper (s - k) k) v)).Finite := by
  simpa using finite_support_pairNO'_heiOper_apply heiTrunc heiComm 0 s v

variable (heiOper)

omit heiComm

/-- `pairNO k l` is symmetric in `k` and `l`. -/
lemma heiOper_pairNO_symm (k l : ℤ) :
    pairNO heiOper k l = pairNO heiOper l k := by
  grind [pairNO]

include heiComm

/-- `pairNO' k l` is symmetric in `k` and `l`. -/
lemma heiOper_pairNO'_symm (k l : ℤ) :
    pairNO' heiOper k l = pairNO' heiOper l k := by
  simpa [← heiOper_pairNO_eq_pairNO' heiComm] using heiOper_pairNO_symm heiOper k l

omit heiComm
include heiTrunc

lemma heiPairNO_trunc_atTop_sub (n : ℤ) (v : V) :
    atTop.Eventually (fun k ↦ pairNO heiOper (n-k) k v = 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (heiTrunc v)
  filter_upwards [Ici_mem_atTop N] with l hl
  rw [Set.mem_Ici] at hl
  by_cases hln : l ≤ n - l
  · simp [pairNO, hln, hN _ (show N ≤ n-l by linarith)]
  · simp [pairNO, hln, hN _ (show N ≤ l by linarith)]

lemma heiPairNO_trunc_atBot_sub (n : ℤ) (v : V) :
    atBot.Eventually (fun k ↦ pairNO heiOper (n-k) k v = 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (heiTrunc v)
  filter_upwards [Iic_mem_atBot (n-N)] with l hl
  rw [Set.mem_Iic] at hl
  by_cases hln : l ≤ n - l
  · simp [pairNO, hln, hN _ (show N ≤ n-l by linarith)]
  · simp [pairNO, hln, hN _ (show N ≤ l by linarith)]

lemma heiPairNO_trunc_cofinite_sub (n : ℤ) (v : V) :
    cofinite.Eventually (fun k ↦ pairNO heiOper (n-k) k v = 0) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (heiPairNO_trunc_atTop_sub heiOper heiTrunc n v)
  obtain ⟨B, hB⟩ := eventually_atBot.mp (heiPairNO_trunc_atBot_sub heiOper heiTrunc n v)
  have filt : (Set.Ioo B T)ᶜ ∈ cofinite :=
    Set.Finite.compl_mem_cofinite (show (Set.Ioo B T).Finite from Set.finite_Ioo B T)
  filter_upwards [filt] with k hkBT
  simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt] at hkBT
  by_cases hk : k ≤ B
  · exact hB k hk
  · exact hT k (hkBT <| by grind only) -- the whole line is `grind`able

open Topology

/-- The basic bosonic Sugawara generators (an auxiliary definition). -/
noncomputable def sugawaraGenAux (n : ℤ) (v : V) : V :=
  (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO heiOper (n-k) k v

omit heiTrunc in
lemma sugawaraGenAux_def (n : ℤ) (v : V) :
    sugawaraGenAux heiOper n v = (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO heiOper (n-k) k v :=
  rfl

omit heiTrunc in
lemma sugawaraGenAux_comp_apply (A : V →ₗ[𝕜] V) (n : ℤ) (v : V) :
    (sugawaraGenAux heiOper n (A v))
      = (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO heiOper (n-k) k (A v) := by
  rw [sugawaraGenAux_def heiOper n (A v)]

variable {heiOper}

lemma comp_sugawaraGenAux_apply (A : V →ₗ[𝕜] V) (n : ℤ) (v : V) :
    A (sugawaraGenAux heiOper n v) = (2 : 𝕜)⁻¹ • ∑ᶠ k, A (pairNO heiOper (n-k) k v) := by
  rw [sugawaraGenAux_def heiOper n v, map_smul, A.map_finsum]
  exact finite_support_pairNO_heiOper_apply₀ heiTrunc n v

lemma sugawaraGenAux_add (n : ℤ) (v w : V) :
    sugawaraGenAux heiOper n (v + w) = sugawaraGenAux heiOper n v + sugawaraGenAux heiOper n w := by
  simp only [sugawaraGenAux_def, map_add, ← smul_add]
  congr 1
  rw [finsum_add_distrib]
  · exact finite_support_pairNO_heiOper_apply₀ heiTrunc n v
  · exact finite_support_pairNO_heiOper_apply₀ heiTrunc n w

variable (heiOper) in
omit heiTrunc in
lemma sugawaraGenAux_smul (n : ℤ) (c : 𝕜) (v : V) :
    sugawaraGenAux heiOper n (c • v) = c • sugawaraGenAux heiOper n v := by
  simp [sugawaraGenAux_def, map_smul, smul_finsum, smul_comm c]

/-- The basic bosonic Sugawara generators (as linear operators). -/
noncomputable def sugawaraGen (n : ℤ) : V →ₗ[𝕜] V where
  toFun := sugawaraGenAux heiOper n
  map_add' v w := sugawaraGenAux_add heiTrunc n v w
  map_smul' c v := sugawaraGenAux_smul heiOper n c v

lemma sugawaraGen_apply (n : ℤ) (v : V) :
    sugawaraGen heiTrunc n v = (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO heiOper (n-k) k v :=
  rfl

lemma sugawaraGen_apply_eq_finsum_shift (n s : ℤ) (v : V) :
    sugawaraGen heiTrunc n v
      = (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO heiOper (n - (k + s)) (k + s) v := by
  rw [sugawaraGen_apply]
  congr 1
  let σ : ℤ ≃ ℤ := ⟨fun n ↦ n + s, fun n ↦ n - s, fun n ↦ by simp, fun n ↦ by simp⟩
  rw [← finsum_comp_equiv σ]
  rfl

lemma commutator_sugawaraGen_apply_eq_finsum_commutator_apply (n : ℤ) (A : V →ₗ[𝕜] V) (v : V) :
    (sugawaraGen heiTrunc n).commutator A v =
      (2 : 𝕜)⁻¹ • ∑ᶠ k, ((pairNO heiOper (n - k) k).commutator A) v := by
  simp only [LinearMap.commutator, LinearMap.sub_apply, Module.End.mul_apply]
  simp_rw [sub_eq_add_neg]
  rw [finsum_add_distrib]
  · rw [smul_add]
    congr
    convert comp_sugawaraGenAux_apply heiTrunc (-A) n v using 1
  · exact finite_support_pairNO_heiOper_apply₀ heiTrunc n (A v)
  · apply (finite_support_pairNO_heiOper_apply₀ heiTrunc n v).subset
    refine Function.support_subset_iff'.mpr ?_
    simp only [Function.mem_support, ne_eq, not_not, neg_eq_zero, ← sub_eq_add_neg]
    intro k hk
    simp [hk]

lemma sugawaraGen_commutator_apply_eq_finsum_commutator_apply (n : ℤ) (A : V →ₗ[𝕜] V) (v : V) :
    A.commutator (sugawaraGen heiTrunc n) v =
      (2 : 𝕜)⁻¹ • ∑ᶠ k, A.commutator (pairNO heiOper (n-k) k) v := by
  rw [LinearMap.commutator_comm, LinearMap.neg_apply]
  rw [commutator_sugawaraGen_apply_eq_finsum_commutator_apply, ← smul_neg, ← finsum_neg_distrib]
  congr 2
  funext j
  rw [LinearMap.commutator_comm, LinearMap.neg_apply, neg_neg]

omit heiTrunc

include heiComm

/-- `[(heiOper l) ∘ (heiOper k), (heiOper m)] = -m * (δ[k+m=0] + δ[l+m=0]) • heiOper (k + l + m)` -/
lemma commutator_heiPair_heiGen (l k m : ℤ) :
    ((heiOper l) * (heiOper k)).commutator (heiOper m)
      = ((-m : 𝕜) * ((if k + m = 0 then 1 else 0)
               + (if l + m = 0 then 1 else 0))) • heiOper (k + l + m) := by
  simp [LinearMap.commutator_pair, heiComm]
  by_cases hkm : k + m = 0
  · simp [show k = -m by linarith]
    by_cases hlm : l + m = 0
    · simp [show l = -m by linarith, mul_add, add_smul]
    · simp [hlm]
  · simp [hkm]
    by_cases hlm : l + m = 0
    · simp [show l = -m by linarith]
    · simp [hlm]

/-- `[:(heiOper l)(heiOper k):, (heiOper m)] = -m * (δ[k+m=0] + δ[l+m=0]) • heiOper (k + l + m)` -/
lemma commutator_heiPairNO_heiGen (l k m : ℤ) :
    (pairNO heiOper l k).commutator (heiOper m)
      = ((-m : 𝕜) * ((if k + m = 0 then 1 else 0)
            + (if l + m = 0 then 1 else 0))) • heiOper (k + l + m) := by
  by_cases hlk : k ≤ l
  · simp [pairNO, hlk]
    have key := @commutator_heiPair_heiGen 𝕜 _ V _ _ heiOper heiComm k l m
    simp only [neg_mul, neg_smul, Module.End.mul_eq_comp] at key ⊢
    rw [key, neg_inj, show k + l + m = l + k + m by ring, add_comm]
  · simp [pairNO, hlk]
    have key := @commutator_heiPair_heiGen 𝕜 _ V _ _ heiOper heiComm l k m
    simp only [Module.End.mul_eq_comp, neg_mul, neg_smul] at key ⊢
    rw [key]

include heiTrunc

/-- `[L(n), J(m)] = -m • J(n+m)` -/
lemma commutator_sugawaraGen_heiOper [CharZero 𝕜] (n m : ℤ) :
    (sugawaraGen heiTrunc n).commutator (heiOper m) = -m • heiOper (n + m) := by
  ext v
  rw [commutator_sugawaraGen_apply_eq_finsum_commutator_apply]
  simp_rw [commutator_heiPairNO_heiGen heiComm]
  simp only [neg_mul, add_sub_cancel, neg_smul, LinearMap.neg_apply, LinearMap.smul_apply,
             zsmul_eq_mul, Module.End.mul_apply, Module.End.intCast_apply]
  simp only [mul_add, mul_ite, mul_one, mul_zero, add_smul, ite_smul, zero_smul]
  rw [finsum_neg_distrib, finsum_add_distrib]
  · rw [finsum_eq_single _ (-m)]
    · simp only [neg_add_cancel, ↓reduceIte]
      rw [finsum_eq_single _ (n + m)]
      · simp only [sub_add_cancel_left, neg_add_cancel, ↓reduceIte]
        simp only [← two_smul (R := 𝕜), ← smul_assoc, smul_eq_mul, smul_neg, ← mul_assoc, neg_inj]
        simp [one_mul]
        norm_cast
      · intro j hjnm
        simp [show n - j + m ≠ 0 by intro con ; apply hjnm ; linarith]
    · intro j hjm
      simp [show j + m ≠ 0 by grind]
  · apply (show Set.Finite {-m} from Set.finite_singleton (-m)).subset
    simp only [Set.subset_singleton_iff, Function.mem_support, ne_eq, ite_eq_right_iff,
               smul_eq_zero, Classical.not_imp, not_or, and_imp]
    intro j hjm _ _
    linarith
  · apply (show Set.Finite {n + m} from Set.finite_singleton (n + m)).subset
    simp only [Set.subset_singleton_iff, Function.mem_support, ne_eq, ite_eq_right_iff,
               smul_eq_zero, Classical.not_imp, not_or, and_imp]
    intro j hjm _ _
    linarith

/-- `[L(n), J(m-k)J(k)] = -k • J(m-k)J(n+k) - (m-k) • J(n+m-k)J(k)` -/
lemma commutator_sugawaraGen_heiOperPair [CharZero 𝕜] (n m k : ℤ) :
    (sugawaraGen heiTrunc n).commutator (heiOper (m-k) * heiOper k)
      = -k • (heiOper (m-k) * heiOper (n+k)) - (m-k) • (heiOper (n+m-k) * heiOper k) := by
  rw [LinearMap.commutator_pair']
  rw [commutator_sugawaraGen_heiOper _ heiComm, commutator_sugawaraGen_heiOper _ heiComm]
  simp only [neg_smul, zsmul_eq_mul, mul_neg, sub_eq_add_neg]
  congr 2
  · simp only [← mul_assoc]
    congr 1
    exact (Int.cast_comm k _).symm
  · simp [show n + (m + -k) = n + m + -k by ring, ← mul_assoc]

/-- `[L(n), :J(m-k)J(k):] = -k • :J(m-k)J(n+k): - (m-k) • :J(n+m-k)J(k): + extra terms • 1` -/
lemma commutator_sugawaraGen_heiPairNO' [CharZero 𝕜] (n m k : ℤ) :
    (sugawaraGen heiTrunc n).commutator (pairNO' heiOper k (m-k))
      = -k • (pairNO' heiOper (n+k) (m-k)
        + if 0 ≤ k ∧ k < -n ∧ n + m = 0 then -(n + k) • 1 else 0
        + if k < 0 ∧ -n ≤ k ∧ n + m = 0 then (n + k) • 1 else 0)
        - (m-k) • (pairNO' heiOper k (n+m-k)) := by
  by_cases hk : 0 ≤ k
  · by_cases hnk : 0 ≤ n + k
    · have hk' : ¬ k < 0 := by linarith
      have hnk' : ¬ k < -n := by linarith
      simp only [pairNO', hk, hk', hnk, hnk', ↓reduceIte, and_false, false_and, add_zero, neg_smul,
        zsmul_eq_mul, Int.cast_sub, ← Module.End.mul_eq_comp]
      simp [commutator_sugawaraGen_heiOperPair heiTrunc heiComm]
    · have hnk' : k < -n := by linarith
      simp only [pairNO', hk, ↓reduceIte, hnk, hnk', neg_smul, zsmul_eq_mul, Int.cast_sub, ←
        Module.End.mul_eq_comp]
      rw [commutator_sugawaraGen_heiOperPair heiTrunc heiComm]
      have aux := (heiComm (n+k) (m-k)) ▸
                  LinearMap.mul_eq_mul_add_commutator (heiOper (n+k)) (heiOper (m-k))
      simp only [aux, show n + k + (m - k) = n + m by ring, neg_smul, zsmul_eq_mul, Int.cast_sub,
                 Int.cast_add, true_and, sub_left_inj, neg_inj]
      simp only [mul_one, neg_add_rev, mul_ite, mul_zero, mul_add (k : V →ₗ[𝕜] V),
                 add_assoc, left_eq_add]
      by_cases hnm : n + m = 0
      · simp only [hnm, ↓reduceIte, Algebra.mul_smul_comm, mul_one, mul_neg]
        simp_rw [add_smul, ← smul_eq_mul, ← add_assoc]
        have (j : ℤ) : Int.cast (R := V →ₗ[𝕜] V) j = Int.cast (R := 𝕜) j • 1 := by norm_cast
        simp [this]
      · simp [hnm]
  · have obs := commutator_sugawaraGen_heiOperPair heiTrunc heiComm n m (m-k)
    simp only [sub_sub_cancel, neg_sub, zsmul_eq_mul, Int.cast_sub,
               show n + m - (m - k) = n + k by ring] at obs
    by_cases hnk : 0 ≤ n + k
    · have hk' : k < 0 := by linarith
      have hnk' : -n ≤ k := by linarith
      simp only [pairNO', hk, hk', hnk, hnk', ↓reduceIte, true_and, false_and, neg_smul,
        zsmul_eq_mul, Int.cast_sub, ← Module.End.mul_eq_comp]
      simp only [obs, add_sub, Int.cast_add, mul_one, zero_add]
      have aux := (heiComm (m-k) (n+k)) ▸
                  LinearMap.mul_eq_mul_add_commutator (heiOper (m-k)) (heiOper (n+k))
      rw [aux, show m - k + (n + k) = n + m by ring]
      rw [sub_eq_add_neg _ ((k : V →ₗ[𝕜] V) * _), sub_eq_add_neg _ ((m - k : V →ₗ[𝕜] V) * _)]
      rw [add_comm _ (-_)]
      simp only [← neg_mul]
      simp only [mul_add (_ : V →ₗ[𝕜] V), add_assoc, add_right_inj]
      by_cases hnm : n + m = 0
      · simp only [hnm, zero_sub, ↓reduceIte, Int.cast_sub, Algebra.mul_smul_comm, mul_one,
                   smul_neg, neg_mul, neg_sub]
        rw [show n = -m by linarith]
        simp only [right_eq_add, sub_eq_add_neg, add_smul, mul_add, ← add_assoc, neg_add, neg_smul,
          neg_neg]
        have (j : ℤ) : Int.cast (R := V →ₗ[𝕜] V) j = Int.cast (R := 𝕜) j • 1 := by norm_cast
        simp [this]
      · simp [hnm]
    · have hk' : k < 0 := by linarith
      have hnk' : ¬ -n ≤ k := by linarith
      simp only [pairNO', hk, hk', hnk, hnk', ↓reduceIte, and_false, false_and, add_zero, neg_smul,
        zsmul_eq_mul, Int.cast_sub, ← Module.End.mul_eq_comp]
      rw [obs]
      rw [sub_eq_add_neg _ ((k : V →ₗ[𝕜] V) * _), sub_eq_add_neg _ ((m - k : V →ₗ[𝕜] V) * _)]
      rw [add_comm _ (-_)]
      simp only [← neg_mul]
      simp only [add_right_inj, add_sub]
      congr 1
      simp

/-- `[L(n), :J(m-k)J(k):] v = -k • :J(m-k)J(n+k): v - (m-k) • :J(n+m-k)J(k): v + extra terms • v` -/
lemma commutator_sugawaraGen_heiPairNO'_apply [CharZero 𝕜] (n m k : ℤ) (v : V) :
    (sugawaraGen heiTrunc n).commutator (pairNO' heiOper k (m-k)) v
      = -k • ((pairNO' heiOper (n+k) (m-k) v)
        + if 0 ≤ k ∧ k < -n ∧ n + m = 0 then -(n + k) • v else 0
        + if k < 0 ∧ -n ≤ k ∧ n + m = 0 then (n + k) • v else 0)
        - (m-k) • (pairNO' heiOper k (n+m-k) v) := by
  have key := LinearMap.congr_fun (commutator_sugawaraGen_heiPairNO' heiTrunc heiComm n m k) v
  simp only [LinearMap.sub_apply] at key
  rw [key]
  simp_rw [smul_add, sub_eq_add_neg, neg_add, LinearMap.add_apply, LinearMap.smul_apply, add_assoc]
  rw [add_right_inj]
  simp only [← add_assoc]
  rw [add_left_inj]
  split_ifs <;> simp [add_smul]

end normal_ordered_pair -- section



section commutator_sugawaraGen

include heiComm in
/-- `[L(n), L(m)] = (n-m) • L(n+m) + (n^3 - n) / 12 * δ[n+m,0] • 1` -/
lemma commutator_sugawaraGen [CharZero 𝕜] (n m : ℤ) :
    (sugawaraGen heiTrunc n).commutator (sugawaraGen heiTrunc m)
      = (n-m) • (sugawaraGen heiTrunc (n+m))
        + if n + m = 0 then ((n ^ 3 - n : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V) else 0 := by
  ext v
  rw [sugawaraGen_commutator_apply_eq_finsum_commutator_apply]
  simp only [heiOper_pairNO_eq_pairNO' heiComm]
  have aux_commutator (k : ℤ) :=
    commutator_sugawaraGen_heiPairNO'_apply heiTrunc heiComm n m (m-k) v
  simp only [show ∀ k, m - (m-k) = k by grind] at aux_commutator
  simp_rw [aux_commutator, sub_eq_add_neg, smul_add, ← add_assoc]
  rw [finsum_add_distrib]
  · simp only [neg_add_rev, neg_neg, le_add_neg_iff_add_le, zero_add, add_neg_lt_iff_lt_add,
               lt_neg_add_iff_add_lt, neg_add_le_iff_le_add, smul_ite, smul_zero, smul_add,
               zsmul_eq_mul, Int.cast_add, Int.cast_neg, LinearMap.add_apply, Module.End.mul_apply,
               Module.End.intCast_apply, LinearMap.neg_apply]
    rw [finsum_add_distrib]
    · simp only [smul_add]
      rw [add_comm, ← add_assoc]
      congr 1
      · -- The dummy index reshuffling.
        rw [← finsum_comp_equiv ⟨fun k ↦ k - n, fun k ↦ k + n, fun _ ↦ by simp, fun _ ↦ by simp⟩]
        dsimp only [Equiv.coe_fn_mk]
        rw [← smul_add, ← finsum_add_distrib]
        · simp only [neg_sub, add_sub_assoc', ← add_assoc]
          simp_rw [show ∀ k, n + m + k - n + -m = k by grind]
          simp_rw [show ∀ k, m + n - k = n + m - k by grind]
          simp_rw [add_smul, sub_smul, ← add_assoc, neg_sub, sub_eq_add_neg]
          simp_rw [neg_add_cancel_right]
          rw [finsum_add_distrib]
          · simp_rw [(Int.cast_smul_eq_zsmul 𝕜 _ _).symm, ← smul_finsum]
            rw [smul_add]
            congr 1 <;>
            · rw [smul_comm]
              simp [← sub_eq_add_neg, heiOper_pairNO_eq_pairNO' heiComm, sugawaraGen_apply]
          · simp_rw [← sub_eq_add_neg]
            exact finite_support_smul_pairNO'_heiOper_apply₀ heiTrunc heiComm ..
          · simp_rw [← sub_eq_add_neg]
            exact finite_support_smul_pairNO'_heiOper_apply₀ heiTrunc heiComm ..
        · have (k : ℤ) : n + m + k - n - m = k := by ring
          simpa [← sub_eq_add_neg, add_sub_assoc', this] using
            finite_support_smul_pairNO'_heiOper_apply₀ heiTrunc heiComm ..
        · simp_rw [← sub_eq_add_neg]
          exact finite_support_smul_pairNO'_heiOper_apply₀ heiTrunc heiComm ..
      · -- The central charge calculation.
        by_cases hnm : n + m = 0
        · have m_eq_neg_n : m = -n := by linarith
          simp only [m_eq_neg_n, add_neg_cancel, and_true, neg_neg, add_zero, zero_add, neg_smul,
                     smul_neg, ↓reduceIte, LinearMap.smul_apply, Module.End.one_apply]
          by_cases hn : 0 ≤ n
          · have obs (i : ℤ) : ¬ (i ≤ -n ∧ 0 < i) := by grind
            simp only [obs, ↓reduceIte]
            rw [finsum_eq_sum_of_support_subset _ (s := Finset.Ioc (-n) 0) ?_]
            · rw [Finset.sum_congr rfl (g := fun i ↦ -(i + n) • i • v)]
              · simp only [← smul_assoc]
                rw [← Finset.sum_smul]
                suffices ((2⁻¹ : 𝕜) * (∑ i ∈ Finset.Ioc (-n) 0, -(i + n) * i)) • v
                            = (((n : 𝕜) ^ 3 + (-n : 𝕜)) / 12) • v by
                  rw [← this, ← smul_eq_mul, smul_assoc]
                  congr 1
                  norm_cast
                congr 1
                have key := bosonic_sugawara_cc_calc 𝕜 n
                rw [zPrimitive_apply_of_nonneg _ (by linarith)] at key
                field_simp at key ⊢
                rw [← sub_eq_add_neg, ← key]
                simp only [mul_assoc]
                norm_num
                rw [@Finset.sum_of_injOn ℕ ℤ 𝕜 _ (Finset.range n.toNat) (Finset.Ioc (-n) 0)
                          (fun x ↦ ↑x * (n - x)) (fun x ↦ (-↑n + -↑x) * x)
                          (fun i ↦ -i) ..]
                · intro i _ j _ hij
                  simpa using hij
                · intro i hi
                  simpa using hi
                · intro k hk hk'
                  exfalso
                  simp only [Finset.mem_Ioc, Finset.coe_range, Set.mem_image, Set.mem_Iio,
                             Int.lt_toNat, not_exists, not_and] at hk hk'
                  apply hk' (-k).toNat ?_
                  · simp [hk.2]
                  · exact (le_of_eq (by simp [hk.2])).trans_lt (show -k < n by linarith)
                · intro k _
                  simp ; ring
              · intro i hi
                simp only [Finset.mem_Ioc.mp hi, and_self, ↓reduceIte, neg_smul]
            · refine Function.support_subset_iff'.mpr ?_
              intro k hk
              simp only [Finset.coe_Ioc, Set.mem_Ioc] at hk
              simp [hk]
          · have obs (i : ℤ) : ¬ (-n < i ∧ i ≤ 0) := by intro maybe ; linarith
            simp only [obs, ↓reduceIte]
            rw [finsum_eq_sum_of_support_subset _ (s := Finset.Ioc 0 (-n)) ?_]
            · rw [Finset.sum_congr rfl (g := fun i ↦ (i + n) • i • v)]
              · simp only [← smul_assoc]
                rw [← Finset.sum_smul]
                suffices ((2⁻¹ : 𝕜) * (∑ i ∈ Finset.Ioc 0 (-n), (i + n) * i)) • v
                            = (((n : 𝕜) ^ 3 + (-n : 𝕜)) / 12) • v by
                  rw [← this, ← smul_eq_mul, smul_assoc]
                  congr 1
                  norm_cast
                congr 1
                have key' := bosonic_sugawara_cc_calc 𝕜 n
                rw [zPrimitive_apply_of_nonpos _ (by linarith)] at key'
                field_simp at key' ⊢
                rw [← sub_eq_add_neg, ← key']
                have aux (k : 𝕜) : (-k - 1) = -(k + 1) := by ring
                simp only [aux, neg_mul, sub_neg_eq_add, neg_mul, mul_assoc,
                           Finset.sum_neg_distrib, neg_mul, neg_neg]
                norm_num
                have n_natAbs : -n = n.natAbs := by
                  simpa [hn] using (abs_of_neg <| not_le.mp hn).symm
                rw [@Finset.sum_of_injOn ℕ ℤ 𝕜 _ (Finset.range n.natAbs) (Finset.Ioc 0 (-n))
                      (fun x ↦ (↑x + 1) * (n + (x + 1))) (fun x ↦ (↑x + ↑n) * x)
                      (fun i ↦ i + 1) ..]
                · intro i _ j _ hij
                  simpa using hij
                · intro i hi
                  simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_Ioc, Set.mem_Ioc,
                             Int.succ_ofNat_pos, true_and, n_natAbs] at hi ⊢
                  exact Int.toNat_le.mp hi
                · intro k hk hk'
                  exfalso
                  simp only [n_natAbs, Finset.mem_Ioc, Finset.coe_range,
                             Set.mem_image, Set.mem_Iio, not_exists, not_and] at hk hk'
                  apply hk' (k - 1).toNat
                  · simp only [Int.pred_toNat]
                    exact (Nat.pred_lt (by simpa using hk.1)).trans_le (by simpa using hk.2)
                  · simp only [Int.pred_toNat]
                    norm_cast
                    rw [Nat.sub_add_eq_max,
                        max_eq_left <| (Int.le_toNat (by linarith)).mpr (show 1 ≤ k by linarith)]
                    exact Int.toNat_of_nonneg (by linarith)
                · intro k _
                  simp ; ring
              · intro i hi
                simp [(Finset.mem_Ioc.mp hi).symm]
            · refine Function.support_subset_iff'.mpr ?_
              intro k hk
              simp only [Finset.coe_Ioc, Set.mem_Ioc, and_comm] at hk
              simp [hk]
        · simp [hnm]
    · simpa [← sub_eq_add_neg] using
        finite_support_smul_pairNO'_heiOper_apply₀ heiTrunc heiComm ..
    · apply ((Set.finite_Ioc (n+m) m).union (Set.finite_Ioc m (n+m))).subset
      refine Function.support_subset_iff'.mpr ?_
      intro k hk
      simp only [Set.Ioc_union_Ioc_symm, Set.mem_Ioc, inf_lt_iff, le_sup_iff] at hk
      grind
  · have aux₀ := finite_support_pairNO'_heiOper_apply heiTrunc heiComm 0 (n + m) v
    simp only [sub_eq_add_neg, zero_add] at aux₀
    apply ((aux₀.union (Set.finite_Ioc (m+n) m)).union (Set.finite_Ioc m (m+n))).subset
    refine Function.support_subset_iff'.mpr ?_
    intro k hk
    simp only [Set.mem_union, Function.mem_support, ne_eq, Set.mem_Ioc, not_or, not_not, not_and,
               not_le] at hk
    rcases hk with ⟨⟨hk₁, hk₂⟩, hk₃⟩
    simp only [neg_add_rev, neg_neg, hk₁, smul_zero, le_add_neg_iff_add_le, zero_add,
               add_neg_lt_iff_lt_add, lt_neg_add_iff_add_lt, neg_add_le_iff_le_add, smul_ite]
    grind
  · have (k : ℤ) : n + m - (m - k) = n + k := by ring
    simp_rw [← sub_eq_add_neg, this, Function.support_neg]
    exact finite_support_smul_pairNO'_heiOper_apply heiTrunc heiComm ..

end commutator_sugawaraGen



section representation

/-- Construct a representation of Virasoro algebra from a central charge value `c` and a
collection `(Lₙ)`, `n ∈ ℤ`, of operators satisfying the commutation relations of Virasoro
generators with that central charge. -/
noncomputable def VirasoroAlgebra.representationOfCentralChargeOfL
    {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]
    {V : Type*} [AddCommGroup V] [Module 𝕂 V] (c : 𝕂) {lOper : ℤ → (V →ₗ[𝕂] V)}
    (lComm : ∀ n m, (lOper n).commutator (lOper m)
      = (n-m) • lOper (n+m) + if n + m = 0 then (c / 12 * (n^3 - n)) • (1 : V →ₗ[𝕂] V) else 0) :
    LieAlgebra.Representation 𝕂 𝕂 (VirasoroAlgebra 𝕂) V := by
    --VirasoroAlgebra 𝕂 →ₗ⁅𝕂⁆ (V →ₗ[𝕂] V) := by
  let ops : Option ℤ → (V →ₗ[𝕂] V) := fun n' ↦ match n' with
    | none => c • 1
    | some n => lOper n
  apply LieAlgebra.representationOfBasis (VirasoroAlgebra.basisLC 𝕂) (genOper := ops)
  intro n' m'
  match n' with
  | none => simp [ops]
  | some n => match m' with
    | none => simp [ops]
    | some m =>
      simp only [ops, lComm, basisLC_some, lgen_bracket, map_add, map_smul]
      congr 1
      · have obs (k : ℤ) : lgen 𝕂 k = (VirasoroAlgebra.basisLC 𝕂) (some k) := by simp
        rw [obs]
        simp only [LieAlgebra.representationOfBasisAux_apply_basis]
        ext v
        simp only [LinearMap.sub_apply, sub_smul, LinearMap.smul_apply]
        congr 1 <;> rw [Int.cast_smul_eq_zsmul]
      · by_cases hnm : n + m = 0
        · have obs : cgen 𝕂 = (VirasoroAlgebra.basisLC 𝕂) none := by simp
          simp only [hnm, ↓reduceIte, map_smul]
          simp only [obs, LieAlgebra.representationOfBasisAux_apply_basis]
          simp only [← smul_assoc, smul_eq_mul]
          congr 1
          field_simp
          rw [mul_comm]
        · simp [hnm]

lemma VirasoroAlgebra.representationOfCentralChargeOfL_cgen
    {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]
    {V : Type*} [AddCommGroup V] [Module 𝕂 V] (c : 𝕂) {lOper : ℤ → (V →ₗ[𝕂] V)}
    (lComm : ∀ n m, (lOper n).commutator (lOper m)
      = (n-m) • lOper (n+m) + if n + m = 0 then (c / 12 * (n^3 - n)) • (1 : V →ₗ[𝕂] V) else 0) :
    (representationOfCentralChargeOfL c lComm) (cgen 𝕂) = c • 1 := by
  convert LieAlgebra.representationOfBasisAux_apply_basis (VirasoroAlgebra.basisLC 𝕂) _ none
  simp

lemma VirasoroAlgebra.representationOfCentralChargeOfL_lgen
    {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]
    {V : Type*} [AddCommGroup V] [Module 𝕂 V] (c : 𝕂) {lOper : ℤ → (V →ₗ[𝕂] V)}
    (lComm : ∀ n m, (lOper n).commutator (lOper m)
      = (n-m) • lOper (n+m) + if n + m = 0 then (c / 12 * (n^3 - n)) • (1 : V →ₗ[𝕂] V) else 0)
    (n : ℤ) :
    (representationOfCentralChargeOfL c lComm) (lgen 𝕂 n) = lOper n := by
  convert LieAlgebra.representationOfBasisAux_apply_basis (VirasoroAlgebra.basisLC 𝕂) _ (some n)
  simp

variable {heiOper} in
/-- **The basic bosonic Sugawara representation of Virasoro algebra (c=1)**:
On a vector space with a representation of the Heisenberg algebra that acts locally truncatedly,
we get a representation of the Virasoro algebra with central charge 1 by the Sugawara
construction. -/
noncomputable def sugawaraRepresentation [CharZero 𝕜] :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V) := by
  apply VirasoroAlgebra.representationOfCentralChargeOfL 1 (lOper := sugawaraGen heiTrunc)
  intro n m
  simp only [commutator_sugawaraGen heiOper heiTrunc heiComm n m, zsmul_eq_mul, Int.cast_sub,
             one_div, add_right_inj]
  by_cases hnm : n + m = 0
  · simp [hnm]
    congr 1
    field_simp
  · simp [hnm]

open VirasoroAlgebra in
/-- The central element `C` of the Virasoro algebra acts as `1` on the representation obtained
by the basic bosonic Sugawara construction. -/
lemma sugawaraRepresentation_cgen [CharZero 𝕜] :
    sugawaraRepresentation heiTrunc heiComm (cgen 𝕜) = 1 := by
  convert VirasoroAlgebra.representationOfCentralChargeOfL_cgen ..
  simp

open VirasoroAlgebra in
/-- The formula for the action of the Virasoro generator `Lₙ` on the representation obtained
by the basic bosonic Sugawara construction. -/
lemma sugawaraRepresentation_lgen_apply' [CharZero 𝕜] (n : ℤ) (v : V) :
    sugawaraRepresentation heiTrunc heiComm (lgen 𝕜 n) v =
      (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO heiOper (n-k) k v := by
  rw [← sugawaraGen_apply heiTrunc]
  apply LinearMap.congr_fun _ v
  convert VirasoroAlgebra.representationOfCentralChargeOfL_lgen ..

open VirasoroAlgebra in
/-- The formula for the action of the Virasoro generator `Lₙ` on the representation obtained
by the basic bosonic Sugawara construction. -/
lemma sugawaraRepresentation_lgen_apply [CharZero 𝕜] (n : ℤ) (v : V) :
    sugawaraRepresentation heiTrunc heiComm (lgen 𝕜 n) v =
      (2 : 𝕜)⁻¹ • ((∑ᶠ k ≥ 0, (heiOper (n-k) ∘ₗ heiOper k) v)
                  + (∑ᶠ k < 0, (heiOper k ∘ₗ heiOper (n-k)) v)) := by
  rw [sugawaraRepresentation_lgen_apply']
  simp_rw [heiOper_pairNO_eq_pairNO' heiComm]
  rw [finsum_add_finsum_compl (Set.Ici 0) _
        (finite_support_pairNO'_heiOper_apply₀ heiTrunc heiComm n v)]
  congr 2
  · simp_rw [heiOper_pairNO'_symm heiOper heiComm]
    simp only [Set.mem_Ici, pairNO', ge_iff_le, LinearMap.coe_comp, Function.comp_apply]
    apply finsum_congr
    intro k
    by_cases hk : 0 ≤ k <;> simp [hk]
  · simp_rw [heiOper_pairNO'_symm heiOper heiComm]
    simp only [Set.compl_Ici, Set.mem_Iio, pairNO', LinearMap.coe_comp, Function.comp_apply]
    apply finsum_congr
    intro k
    by_cases hk : k < 0
    · have hk' : ¬ 0 ≤ k := by linarith
      simp [hk, hk']
    · simp [hk]

end representation

section heisenberg_representation

omit heiOper heiTrunc heiComm in
open HeisenbergAlgebra in
-- TODO: Generalize to `kgen` acting as `κ • 1`, maybe.
/-- **The basic bosonic Sugawara representation of Virasoro algebra (c=1)**:
On a vector space with a representation of the Heisenberg algebra that acts locally truncatedly
(and the central element `k` acts as `1`), we get a representation of the Virasoro algebra with
central charge `c = 1` by the Sugawara construction. -/
noncomputable def sugawaraRepresentation_of_representation_heisenbergAlgebra [CharZero 𝕜]
    (α : LieAlgebra.Representation 𝕜 𝕜 (HeisenbergAlgebra 𝕜) V)
    (hα : ∀ v, ∀ᶠ k in atTop, α (jgen _ k) v = 0) (hαc : α (kgen _) = 1) :
    LieAlgebra.Representation 𝕜 𝕜 (VirasoroAlgebra 𝕜) V := by
  apply sugawaraRepresentation hα
  intro k l
  simp [← LieAlgebra.Representation.apply_bracket_eq_commutator α (jgen _ k) (jgen _ l)]
  by_cases hkl : k + l = 0
  · simp [hkl, hαc]
  · simp [hkl]

end heisenberg_representation

end Sugawara_boson -- section

end VirasoroProject -- namespace
