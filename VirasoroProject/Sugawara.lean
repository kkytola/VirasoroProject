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
import VirasoroProject.ToMathlib.Topology.Algebra.BigOperators.FinProd
import Mathlib

attribute [local instance 100] LieRing.ofAssociativeRing

/-!
# The bosonic Sugawara construction

Given a family of operators `J k`, `k ∈ ℤ`, on a vector space `V` over a field `𝕜` of
characteristic zero, subject to the Heisenberg algebra commutation relations
`[J k, J l] = k δ[k+l=0] • 1` (`heiComm`) and acting in a locally truncated way (`heiTrunc`),
this file defines the Sugawara operators `L n = 2⁻¹ • ∑ᶠ k, :J (n-k) J k:` and proves that they
satisfy the Virasoro commutation relations with central charge `c = 1`.

## Main definitions

* `VirasoroProject.pairNO`: the normal-ordered pair `:J k J l:`.
* `VirasoroProject.sugawaraGen`: the Sugawara operators `L n`, `n ∈ ℤ`, as linear maps.
* `VirasoroAlgebra.representationOfCentralChargeOfL`: A variant of the construction
  (`LieAlgebra.representationOfBasis`) of a representation of a Lie algebra from operators
  corresponding to a basis, for the special case of the Virasoro algebra: a representation is
  constructed from operators corresponding to the `lgen` Virasoro generators satisfying
  commutation relations with a given central charge `c`.
* `VirasoroProject.sugawaraRepresentation`: Any representation of the Heisenberg algebra
  where the Heisenberg modes act in a locally truncated fashion can be made into a representation
  of the Virasoro algebra with central charge `c = 1` by the (basic) bosonic Sugawara construction.

## Main statements

* `VirasoroProject.commutator_sugawaraGen_heiOper`: `[L n, J m] = -m • J (n+m)`, i.e., the
  Heisenberg field is primary of conformal weight `1`.
* `VirasoroProject.commutator_sugawaraGen`: the Virasoro commutation relations
  `[L n, L m] = (n-m) • L (n+m) + δ[n+m=0] • ((n³-n)/12) • 1` (central charge `c = 1`).
* `VirasoroProject.sugawaraRepresentation_lgen_apply`: In `VirasoroProject.sugawaraRepresentation`,
  the Virasoro generators `lgen _ n`, `n ∈ ℤ`, act by the Sugawara formula
  `Lₙ = 1/2 • ∑ k ≥ 0, J(n-k) ∘ J(k) + 1/2 • ∑ k < 0, J(k) ∘ J(n-k)`.
* `VirasoroProject.sugawaraRepresentation_cgen`: In `VirasoroProject.sugawaraRepresentation`,
  the central charge is `c = 1`, i.e., the Virasoro generator `cgen _` acts as `1 • id`.

## Tags

Sugawara construction, Virasoro algebra, Heisenberg algebra, bosonic Fock space

-/

namespace VirasoroProject



section Sugawara_boson

open Filter

variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

variable (heiOper : ℤ → (V →ₗ[𝕜] V))
variable (heiTrunc : ∀ v, ∀ᶠ l in atTop, (heiOper l) v = 0)
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
  rcases le_sup_iff.mp h with k_large | l_large
  · by_cases hlk : l ≤ k
    · simp [pairNO, hlk, A_trunc k k_large]
    · simp [pairNO, hlk, A_trunc l (by linarith)]
  · by_cases hlk : l ≤ k
    · simp [pairNO, hlk, A_trunc k (by linarith)]
    · simp [pairNO, hlk, A_trunc l l_large]

include heiComm in
/-- `heiOper k` and `heiOper l` commute unless `k + l = 0`. -/
lemma heiComm_of_add_ne_zero {k l : ℤ} (hkl : k + l ≠ 0) :
    (heiOper k) ∘ₗ (heiOper l) = (heiOper l) ∘ₗ (heiOper k) := by
  simpa [hkl, sub_eq_zero, LinearMap.commutator, Module.End.mul_eq_comp] using heiComm k l

variable {heiOper}

include heiComm in
/-- The two definitions of normal ordered pairs coincide. -/
lemma heiOper_pairNO_eq_pairNO' (k l : ℤ) :
    pairNO heiOper k l = pairNO' heiOper k l := by
  unfold pairNO pairNO'
  by_cases hk : 0 ≤ k
  · simp only [hk, ↓reduceIte, ite_eq_left_iff, not_le]
    intro hkl
    exact heiComm_of_add_ne_zero heiOper heiComm (by linarith)
  · simp only [hk, ↓reduceIte, ite_eq_right_iff]
    intro hlk
    exact heiComm_of_add_ne_zero heiOper heiComm (by linarith)

include heiComm in
/-- The normal-ordered pair as the raw product minus an explicit boundary term:
`:J k J l:' = J k * J l - δ[0 ≤ k] δ[k+l=0] k • 1`.

This is the key to computing commutators with normal-ordered pairs: the boundary term is
central, so all commutator computations can be done with raw products. -/
lemma pairNO'_eq_mul_sub_boundary (k l : ℤ) :
    pairNO' heiOper k l
      = heiOper k * heiOper l - (if 0 ≤ k ∧ k + l = 0 then (k : 𝕜) else 0) • 1 := by
  by_cases hk : 0 ≤ k
  · simp only [pairNO', hk, ↓reduceIte, true_and, ← Module.End.mul_eq_comp]
    rw [LinearMap.mul_eq_mul_add_commutator (heiOper l) (heiOper k), heiComm l k]
    by_cases hkl : k + l = 0
    · obtain rfl : l = -k := by omega
      simp only [add_neg_cancel, ↓reduceIte, neg_add_cancel, Int.cast_neg, neg_smul]
      abel
    · simp [hkl, show ¬ l + k = 0 by omega]
  · simp [pairNO', hk, Module.End.mul_eq_comp]

variable (heiOper) in
/-- `pairNO k l` is symmetric in `k` and `l`. -/
lemma heiOper_pairNO_symm (k l : ℤ) :
    pairNO heiOper k l = pairNO heiOper l k := by
  grind [pairNO]

include heiComm in
/-- `pairNO' k l` is symmetric in `k` and `l`. -/
lemma heiOper_pairNO'_symm (k l : ℤ) :
    pairNO' heiOper k l = pairNO' heiOper l k := by
  simpa [← heiOper_pairNO_eq_pairNO' heiComm] using heiOper_pairNO_symm heiOper k l

include heiTrunc in
/-- As a function of `k`, the normal-ordered pair `:J (n-k) J (m+k): v` has finite support:
both indices tend to `±∞` with `k`, and the larger one eventually annihilates `v`. -/
lemma hasFiniteSupport_pairNO_apply (n m : ℤ) (v : V) :
    Function.HasFiniteSupport fun k ↦ pairNO heiOper (n - k) (m + k) v := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, heiOper k v = 0 := mem_atTop_sets.mp (heiTrunc v)
  apply (Set.finite_Ioo (n - N) (N - m)).subset
  intro k hk
  simp only [Function.mem_support, ne_eq] at hk
  have key : ¬ N ≤ max (n - k) (m + k) :=
    fun maybe_large ↦ hk (pairNO_apply_eq_zero heiOper hN maybe_large)
  simp only [Set.mem_Ioo]
  omega

include heiTrunc in
/-- The special case of `hasFiniteSupport_pairNO_apply` with the index pattern `n-k, k` of
the Sugawara operators. -/
lemma hasFiniteSupport_pairNO_apply' (s : ℤ) (v : V) :
    Function.HasFiniteSupport fun k ↦ pairNO heiOper (s - k) k v := by
  simpa using hasFiniteSupport_pairNO_apply heiTrunc s 0 v

include heiTrunc in
/-- Weighted version of `hasFiniteSupport_pairNO_apply`. -/
lemma hasFiniteSupport_smul_pairNO_apply {𝕂 : Type*} [Zero 𝕂] [SMulZeroClass 𝕂 V]
    (c : ℤ → 𝕂) (n m : ℤ) (v : V) :
    Function.HasFiniteSupport fun k ↦ c k • pairNO heiOper (n - k) (m + k) v :=
  (hasFiniteSupport_pairNO_apply heiTrunc n m v).smul_right c

include heiTrunc in
/-- Weighted version of `hasFiniteSupport_pairNO_apply'`. -/
lemma hasFiniteSupport_smul_pairNO_apply' {𝕂 : Type*} [Zero 𝕂] [SMulZeroClass 𝕂 V]
    (c : ℤ → 𝕂) (s : ℤ) (v : V) :
    Function.HasFiniteSupport fun k ↦ c k • pairNO heiOper (s - k) k v :=
  (hasFiniteSupport_pairNO_apply' heiTrunc s v).smul_right c

include heiTrunc heiComm in
/-- Version of `hasFiniteSupport_pairNO_apply` for the sign-based normal ordering `pairNO'`. -/
lemma hasFiniteSupport_pairNO'_apply (n m : ℤ) (v : V) :
    Function.HasFiniteSupport fun k ↦ pairNO' heiOper (n - k) (m + k) v := by
  simp_rw [← heiOper_pairNO_eq_pairNO' heiComm]
  exact hasFiniteSupport_pairNO_apply heiTrunc n m v

include heiTrunc heiComm in
/-- Version of `hasFiniteSupport_pairNO_apply'` for the sign-based normal ordering `pairNO'`. -/
lemma hasFiniteSupport_pairNO'_apply' (s : ℤ) (v : V) :
    Function.HasFiniteSupport fun k ↦ pairNO' heiOper (s - k) k v := by
  simp_rw [← heiOper_pairNO_eq_pairNO' heiComm]
  exact hasFiniteSupport_pairNO_apply' heiTrunc s v

include heiTrunc heiComm in
/-- Weighted version of `hasFiniteSupport_pairNO'_apply`. -/
lemma hasFiniteSupport_smul_pairNO'_apply {𝕂 : Type*} [Zero 𝕂] [SMulZeroClass 𝕂 V]
    (c : ℤ → 𝕂) (n m : ℤ) (v : V) :
    Function.HasFiniteSupport fun k ↦ c k • pairNO' heiOper (n - k) (m + k) v :=
  (hasFiniteSupport_pairNO'_apply heiTrunc heiComm n m v).smul_right c

include heiTrunc heiComm in
/-- Weighted version of `hasFiniteSupport_pairNO'_apply'`. -/
lemma hasFiniteSupport_smul_pairNO'_apply' {𝕂 : Type*} [Zero 𝕂] [SMulZeroClass 𝕂 V]
    (c : ℤ → 𝕂) (s : ℤ) (v : V) :
    Function.HasFiniteSupport fun k ↦ c k • pairNO' heiOper (s - k) k v :=
  (hasFiniteSupport_pairNO'_apply' heiTrunc heiComm s v).smul_right c

variable (heiOper)

/-- The basic bosonic Sugawara generators (an auxiliary definition). -/
noncomputable def sugawaraGenAux (n : ℤ) (v : V) : V :=
  (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO heiOper (n-k) k v

lemma sugawaraGenAux_def (n : ℤ) (v : V) :
    sugawaraGenAux heiOper n v = (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO heiOper (n-k) k v :=
  rfl

variable {heiOper}

include heiTrunc in
lemma sugawaraGenAux_add (n : ℤ) (v w : V) :
    sugawaraGenAux heiOper n (v + w) = sugawaraGenAux heiOper n v + sugawaraGenAux heiOper n w := by
  simp only [sugawaraGenAux_def, map_add, ← smul_add]
  congr 1
  exact finsum_add_distrib (hasFiniteSupport_pairNO_apply' heiTrunc n v)
    (hasFiniteSupport_pairNO_apply' heiTrunc n w)

variable (heiOper) in
lemma sugawaraGenAux_smul (n : ℤ) (c : 𝕜) (v : V) :
    sugawaraGenAux heiOper n (c • v) = c • sugawaraGenAux heiOper n v := by
  simp [sugawaraGenAux_def, map_smul, smul_finsum, smul_comm c]

/-- The basic bosonic Sugawara generators (as linear operators). -/
noncomputable def sugawaraGen (n : ℤ) : V →ₗ[𝕜] V where
  toFun := sugawaraGenAux heiOper n
  map_add' v w := sugawaraGenAux_add heiTrunc n v w
  map_smul' c v := sugawaraGenAux_smul heiOper n c v

/-- The defining formula of the basic bosonic Sugawara generators. -/
lemma sugawaraGen_apply (n : ℤ) (v : V) :
    sugawaraGen heiTrunc n v = (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO heiOper (n-k) k v :=
  rfl

/-- Any operator `A` distributes over the defining sum of the Sugawara generators (local
truncation allows interchanging `A` with the `finsum`). -/
lemma comp_sugawaraGen_apply (A : V →ₗ[𝕜] V) (n : ℤ) (v : V) :
    A (sugawaraGen heiTrunc n v) = (2 : 𝕜)⁻¹ • ∑ᶠ k, A (pairNO heiOper (n-k) k v) := by
  rw [sugawaraGen_apply, map_smul, map_finsum A (hasFiniteSupport_pairNO_apply' heiTrunc n v)]

/-- The commutator of a Sugawara generator with any operator `A`, applied to a vector, expanded
as a sum of commutators with the normal-ordered pairs. -/
lemma commutator_sugawaraGen_apply_eq_finsum_commutator_apply (n : ℤ) (A : V →ₗ[𝕜] V) (v : V) :
    (sugawaraGen heiTrunc n).commutator A v =
      (2 : 𝕜)⁻¹ • ∑ᶠ k, ((pairNO heiOper (n - k) k).commutator A) v := by
  have h₁ : Function.HasFiniteSupport fun k ↦ pairNO heiOper (n-k) k (A v) :=
    hasFiniteSupport_pairNO_apply' heiTrunc n (A v)
  have h₂ : Function.HasFiniteSupport fun k ↦ A (pairNO heiOper (n-k) k v) :=
    (hasFiniteSupport_pairNO_apply' heiTrunc n v).fun_comp (map_zero A)
  calc (sugawaraGen heiTrunc n).commutator A v
      = sugawaraGen heiTrunc n (A v) - A (sugawaraGen heiTrunc n v) := rfl
    _ = (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO heiOper (n-k) k (A v)
        - (2 : 𝕜)⁻¹ • ∑ᶠ k, A (pairNO heiOper (n-k) k v) := by
      rw [sugawaraGen_apply, comp_sugawaraGen_apply heiTrunc]
    _ = (2 : 𝕜)⁻¹ • ∑ᶠ k, (pairNO heiOper (n-k) k (A v) - A (pairNO heiOper (n-k) k v)) := by
      rw [← smul_sub, ← finsum_sub_distrib h₁ h₂]
    _ = (2 : 𝕜)⁻¹ • ∑ᶠ k, ((pairNO heiOper (n - k) k).commutator A) v := by
      refine congrArg _ (finsum_congr fun k ↦ ?_)
      simp [LinearMap.commutator]

/-- Variant of `commutator_sugawaraGen_apply_eq_finsum_commutator_apply` with the Sugawara
generator in the second slot of the commutator. -/
lemma sugawaraGen_commutator_apply_eq_finsum_commutator_apply (n : ℤ) (A : V →ₗ[𝕜] V) (v : V) :
    A.commutator (sugawaraGen heiTrunc n) v =
      (2 : 𝕜)⁻¹ • ∑ᶠ k, A.commutator (pairNO heiOper (n-k) k) v := by
  rw [LinearMap.commutator_comm, LinearMap.neg_apply,
      commutator_sugawaraGen_apply_eq_finsum_commutator_apply, ← smul_neg, ← finsum_neg_distrib]
  congr 2
  funext k
  rw [LinearMap.commutator_comm, LinearMap.neg_apply, neg_neg]

variable (heiOper)

include heiComm in
/-- `[(heiOper l) (heiOper k), heiOper m] = -m * (δ[k+m=0] + δ[l+m=0]) • heiOper (k + l + m)` -/
lemma commutator_heiPair_heiGen (l k m : ℤ) :
    ((heiOper l) * (heiOper k)).commutator (heiOper m)
      = ((-m : 𝕜) * ((if k + m = 0 then 1 else 0)
               + (if l + m = 0 then 1 else 0))) • heiOper (k + l + m) := by
  simp only [LinearMap.commutator_pair, heiComm]
  by_cases hkm : k + m = 0
  · by_cases hlm : l + m = 0
    · simp [show k = -m by omega, show l = -m by omega, mul_add, add_smul]
    · simp [hlm, show k = -m by omega]
  · by_cases hlm : l + m = 0
    · simp [hkm, show l = -m by omega]
    · simp [hkm, hlm]

include heiComm in
/-- `[:(heiOper l)(heiOper k):, heiOper m] = -m * (δ[k+m=0] + δ[l+m=0]) • heiOper (k + l + m)` -/
lemma commutator_heiPairNO_heiGen (l k m : ℤ) :
    (pairNO heiOper l k).commutator (heiOper m)
      = ((-m : 𝕜) * ((if k + m = 0 then 1 else 0)
            + (if l + m = 0 then 1 else 0))) • heiOper (k + l + m) := by
  by_cases hlk : k ≤ l
  · simp only [pairNO, hlk, ↓reduceIte, ← Module.End.mul_eq_comp]
    rw [commutator_heiPair_heiGen heiOper heiComm k l m,
        show l + k + m = k + l + m by ring, add_comm (if l + m = 0 then (1 : 𝕜) else 0)]
  · simp only [pairNO, hlk, ↓reduceIte, ← Module.End.mul_eq_comp]
    exact commutator_heiPair_heiGen heiOper heiComm l k m

variable {heiOper}

include heiComm in
/-- `[L(n), J(m)] = -m • J(n+m)` -/
lemma commutator_sugawaraGen_heiOper [CharZero 𝕜] (n m : ℤ) :
    (sugawaraGen heiTrunc n).commutator (heiOper m) = -(m : 𝕜) • heiOper (n + m) := by
  ext v
  have h₁ : Function.HasFiniteSupport
      fun k : ℤ ↦ if k + m = 0 then -(m : 𝕜) • heiOper (n + m) v else 0 := by
    apply (Set.finite_singleton (-m)).subset
    intro k hk
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hk
    simp only [Set.mem_singleton_iff]
    omega
  have h₂ : Function.HasFiniteSupport
      fun k : ℤ ↦ if n - k + m = 0 then -(m : 𝕜) • heiOper (n + m) v else 0 := by
    apply (Set.finite_singleton (n + m)).subset
    intro k hk
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hk
    simp only [Set.mem_singleton_iff]
    omega
  calc (sugawaraGen heiTrunc n).commutator (heiOper m) v
      = (2 : 𝕜)⁻¹ • ∑ᶠ k, ((pairNO heiOper (n - k) k).commutator (heiOper m)) v :=
        commutator_sugawaraGen_apply_eq_finsum_commutator_apply heiTrunc n (heiOper m) v
    -- Each commutator with a normal-ordered pair contributes two delta terms.
    _ = (2 : 𝕜)⁻¹ • ∑ᶠ k, ((if k + m = 0 then -(m : 𝕜) • heiOper (n + m) v else 0)
          + (if n - k + m = 0 then -(m : 𝕜) • heiOper (n + m) v else 0)) := by
        refine congrArg _ (finsum_congr fun k ↦ ?_)
        rw [commutator_heiPairNO_heiGen heiOper heiComm (n - k) k m,
            show k + (n - k) + m = n + m by ring]
        simp only [mul_add, mul_ite, mul_one, mul_zero, add_smul, ite_smul, zero_smul,
                   LinearMap.add_apply, DFunLike.ite_apply, LinearMap.zero_apply,
                   LinearMap.smul_apply]
    -- The two delta families are supported at the single points `k = -m` and `k = n + m`.
    _ = (2 : 𝕜)⁻¹ • ((∑ᶠ k, if k + m = 0 then -(m : 𝕜) • heiOper (n + m) v else 0)
          + ∑ᶠ k, if n - k + m = 0 then -(m : 𝕜) • heiOper (n + m) v else 0) := by
        rw [finsum_add_distrib h₁ h₂]
    _ = (2 : 𝕜)⁻¹ • (-(m : 𝕜) • heiOper (n + m) v + -(m : 𝕜) • heiOper (n + m) v) := by
        rw [finsum_eq_single _ (-m) (fun k hk ↦ by simp [show ¬ k + m = 0 by omega]),
            finsum_eq_single _ (n + m) (fun k hk ↦ by simp [show ¬ n - k + m = 0 by omega]),
            if_pos (by omega), if_pos (by omega)]
    _ = -(m : 𝕜) • heiOper (n + m) v := by
        rw [← two_smul 𝕜, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    _ = (-(m : 𝕜) • heiOper (n + m)) v := rfl

include heiComm in
/-- `[L(n), J(k) J(l)] = -l • (J(k) J(n+l)) + -k • (J(n+k) J(l))` -/
lemma commutator_sugawaraGen_mul [CharZero 𝕜] (n k l : ℤ) :
    (sugawaraGen heiTrunc n).commutator (heiOper k * heiOper l)
      = -(l : 𝕜) • (heiOper k * heiOper (n + l)) + -(k : 𝕜) • (heiOper (n + k) * heiOper l) := by
  rw [LinearMap.commutator_pair']
  simp [commutator_sugawaraGen_heiOper heiTrunc heiComm, Algebra.mul_smul_comm,
        Algebra.smul_mul_assoc]

include heiComm in
/-- `[L n, :J (m-k) J k:'] = -k • :J (m-k) J (n+k):' - (m-k) • :J (n+m-k) J k:' + bdry • 1`,
where the boundary coefficient `bdry = k (n+k) (δ[k+n≤0] - δ[k≤0])` is present only if
`n + m = 0`. -/
lemma commutator_sugawaraGen_heiPairNO' [CharZero 𝕜] (n m k : ℤ) :
    (sugawaraGen heiTrunc n).commutator (pairNO' heiOper (m - k) k)
      = -(k : 𝕜) • pairNO' heiOper (m - k) (n + k)
        + -((m : 𝕜) - k) • pairNO' heiOper (n + m - k) k
        + (if n + m = 0 then
             (k : 𝕜) * ((n : 𝕜) + k)
               * ((if k + n ≤ 0 then (1 : 𝕜) else 0) - (if k ≤ 0 then (1 : 𝕜) else 0))
           else 0) • 1 := by
  -- The boundary part of the normal-ordered pair is central, so the commutator only sees the
  -- raw product.
  have first : (sugawaraGen heiTrunc n).commutator (pairNO' heiOper (m - k) k)
      = (sugawaraGen heiTrunc n).commutator (heiOper (m - k) * heiOper k) := by
    rw [pairNO'_eq_mul_sub_boundary heiComm (m - k) k, sub_eq_add_neg, ← neg_smul,
        LinearMap.commutator_add, LinearMap.commutator_smul_one, add_zero]
  rw [first, commutator_sugawaraGen_mul heiTrunc heiComm,
      show n + (m - k) = n + m - k by ring,
      pairNO'_eq_mul_sub_boundary heiComm (m - k) (n + k),
      pairNO'_eq_mul_sub_boundary heiComm (n + m - k) k]
  by_cases hnm : n + m = 0
  · obtain rfl : m = -n := by omega
    match_scalars
    · ring
    · ring
    · split_ifs <;> first | (exfalso; omega) | ring
  · have h₁ : ¬ (0 ≤ m - k ∧ (m - k) + (n + k) = 0) := by omega
    have h₂ : ¬ (0 ≤ n + m - k ∧ (n + m - k) + k = 0) := by omega
    simp only [hnm, h₁, h₂, if_false, zero_smul, sub_zero, add_zero]
    match_scalars <;> ring

include heiTrunc heiComm in
/-- The normal-ordered part of `∑ᶠ k, [L n, :J (m-k) J k:']`: after an index shift, the two
families of terms combine into `(n - m) • ∑ᶠ k, :J (n+m-k) J k:'`. -/
private lemma sugawaraGen_NO_sum [CharZero 𝕜] (n m : ℤ) (v : V) :
    ∑ᶠ k : ℤ, (-(k : 𝕜) • pairNO' heiOper (m - k) (n + k) v
        + -((m : 𝕜) - k) • pairNO' heiOper (n + m - k) k v)
      = ((n : 𝕜) - m) • ∑ᶠ k : ℤ, pairNO' heiOper (n + m - k) k v := by
  -- Variable change: shift `k ↦ k - n` in the first summand.
  have var_change : ∑ᶠ k : ℤ, -(k : 𝕜) • pairNO' heiOper (m - k) (n + k) v
      = ∑ᶠ k : ℤ, ((n : 𝕜) - k) • pairNO' heiOper (n + m - k) k v := by
    rw [← finsum_comp_equiv (Equiv.subRight n)]
    refine finsum_congr fun k ↦ ?_
    simp only [Equiv.subRight_apply]
    rw [show m - (k - n) = n + m - k by ring, show n + (k - n) = k by ring]
    congr 1
    push_cast
    ring
  calc  ∑ᶠ k : ℤ, (-(k : 𝕜) • pairNO' heiOper (m - k) (n + k) v
            + -((m : 𝕜) - k) • pairNO' heiOper (n + m - k) k v)
    -- Split into the two summands.
    _ = ∑ᶠ k : ℤ, -(k : 𝕜) • pairNO' heiOper (m - k) (n + k) v
          + ∑ᶠ k : ℤ, -((m : 𝕜) - k) • pairNO' heiOper (n + m - k) k v :=
        finsum_add_distrib ?_ ?_
    -- Shift the first summand by `k ↦ k - n` via `var_change`.
    _ = ∑ᶠ k : ℤ, ((n : 𝕜) - k) • pairNO' heiOper (n + m - k) k v
          + ∑ᶠ k : ℤ, -((m : 𝕜) - k) • pairNO' heiOper (n + m - k) k v := by rw [var_change]
    -- Recombine into a single sum over a common `pairNO'` factor.
    _ = ∑ᶠ k : ℤ, (((n : 𝕜) - k) • pairNO' heiOper (n + m - k) k v
          + -((m : 𝕜) - k) • pairNO' heiOper (n + m - k) k v) := (finsum_add_distrib ?_ ?_).symm
    -- Combine the coefficients: `(n - k) + (k - m) = n - m`.
    _ = ∑ᶠ k : ℤ, ((n : 𝕜) - m) • pairNO' heiOper (n + m - k) k v := by
        refine finsum_congr fun k ↦ ?_
        rw [← add_smul]
        congr 1
        ring
    -- Pull out the constant scalar.
    _ = ((n : 𝕜) - m) • ∑ᶠ k : ℤ, pairNO' heiOper (n + m - k) k v :=
        (smul_finsum' _ (hasFiniteSupport_pairNO'_apply' heiTrunc heiComm (n + m) v)).symm
  -- Finiteness side conditions, in the order the `?_`s above were introduced.
  · exact hasFiniteSupport_smul_pairNO'_apply heiTrunc heiComm _ m n v
  · exact hasFiniteSupport_smul_pairNO'_apply' heiTrunc heiComm _ (n + m) v
  · exact hasFiniteSupport_smul_pairNO'_apply' heiTrunc heiComm _ (n + m) v
  · exact hasFiniteSupport_smul_pairNO'_apply' heiTrunc heiComm _ (n + m) v

/-- The central-charge summand: the boundary term of `commutator_sugawaraGen_heiPairNO'` at
`n + m = 0`, as a function of the summation index `k`. -/
private def ccTermInt (n k : ℤ) : 𝕜 :=
  (k : 𝕜) * ((n : 𝕜) + k)
    * ((if k + n ≤ 0 then (1 : 𝕜) else 0) - (if k ≤ 0 then (1 : 𝕜) else 0))

private lemma ccTermInt_eq_zero_of_not_mem (n k : ℤ)
    (hk : k < min 0 (-n) ∨ max 0 (-n) < k) :
    ccTermInt (𝕜 := 𝕜) n k = 0 := by
  rcases hk with hk | hk
  · simp [ccTermInt, show k + n ≤ 0 by omega, show k ≤ 0 by omega]
  · simp [ccTermInt, show ¬ k + n ≤ 0 by omega, show ¬ k ≤ 0 by omega]

private lemma hasFiniteSupport_ccTermInt (n : ℤ) :
    Function.HasFiniteSupport fun k : ℤ ↦ ccTermInt (𝕜 := 𝕜) n k := by
  apply (Set.finite_Icc (min 0 (-n)) (max 0 (-n))).subset
  intro k hk
  simp only [Function.mem_support, ne_eq] at hk
  simp only [Set.mem_Icc]
  by_contra hk'
  exact hk (ccTermInt_eq_zero_of_not_mem n k (by omega))

/-- The bosonic central charge sum: `∑ₖ CC_k(n) = (n³-n)/6` where `CC_k(n)` are the boundary
terms from `commutator_sugawaraGen_heiPairNO'` with `m = -n`. The sum is a quadratic-polynomial
sum over an integer interval, evaluated in closed form by `sum_Ico_quadratic`. -/
private lemma sugawaraGen_cc_sum [CharZero 𝕜] (n : ℤ) :
    ∑ᶠ k : ℤ, ccTermInt (𝕜 := 𝕜) n k = ((n : 𝕜) ^ 3 - n) / 6 := by
  rcases le_total 0 n with hn | hn
  · -- `0 ≤ n`: the boundary terms are supported on `[-n, 0]`, where they are the quadratic
    -- polynomial `-k (n + k)`.
    rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.Ico (-n) 1) ?_]
    · rw [Finset.sum_congr rfl
            (g := fun x : ℤ ↦ (-1 : 𝕜) * (x : 𝕜) ^ 2 + (-(n : 𝕜)) * (x : 𝕜) + 0) ?_,
          sum_Ico_quadratic (-n) 1 (by omega)]
      · push_cast; ring
      · intro x hx
        simp only [Finset.mem_Ico] at hx
        by_cases hxn : x + n ≤ 0
        · obtain rfl : x = -n := by omega
          simp only [ccTermInt]
          push_cast
          ring
        · simp only [ccTermInt, if_neg hxn, if_pos (show x ≤ 0 by omega)]
          ring
    · intro k hk
      simp only [Function.mem_support, ne_eq] at hk
      simp only [Finset.coe_Ico, Set.mem_Ico]
      by_contra hk'
      exact hk (ccTermInt_eq_zero_of_not_mem n k (by omega))
  · -- `n ≤ 0`: the boundary terms are supported on `[1, -n]`, where they are the quadratic
    -- polynomial `k (n + k)`.
    rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.Ico 1 (1 - n)) ?_]
    · rw [Finset.sum_congr rfl
            (g := fun x : ℤ ↦ (1 : 𝕜) * (x : 𝕜) ^ 2 + ((n : 𝕜)) * (x : 𝕜) + 0) ?_,
          sum_Ico_quadratic 1 (1 - n) (by omega)]
      · push_cast; ring
      · intro x hx
        simp only [Finset.mem_Ico] at hx
        simp only [ccTermInt, if_pos (show x + n ≤ 0 by omega), if_neg (show ¬ x ≤ 0 by omega)]
        ring
    · intro k hk
      simp only [Function.mem_support, ne_eq] at hk
      simp only [Finset.coe_Ico, Set.mem_Ico]
      by_contra hk'
      apply hk
      rcases (by omega : k ≤ 0 ∨ -n < k) with h | h
      · simp [ccTermInt, h, show k + n ≤ 0 by omega]
      · simp [ccTermInt, show ¬ k ≤ 0 by omega, show ¬ k + n ≤ 0 by omega]

include heiComm in
/-- **The Virasoro commutation relations for the bosonic Sugawara operators**:
`[L(n), L(m)] = (n-m) • L(n+m) + δ[n+m=0] (n³-n)/12 • 1`. -/
lemma commutator_sugawaraGen [CharZero 𝕜] (n m : ℤ) :
    (sugawaraGen heiTrunc n).commutator (sugawaraGen heiTrunc m)
      = ((n : 𝕜) - m) • (sugawaraGen heiTrunc (n+m))
        + if n + m = 0 then (((n : 𝕜) ^ 3 - n) / 12) • (1 : V →ₗ[𝕜] V) else 0 := by
  ext v
  have hNO : Function.HasFiniteSupport fun k : ℤ ↦
      -(k : 𝕜) • pairNO' heiOper (m - k) (n + k) v
        + -((m : 𝕜) - k) • pairNO' heiOper (n + m - k) k v :=
    (hasFiniteSupport_smul_pairNO'_apply heiTrunc heiComm _ m n v).add
      (hasFiniteSupport_smul_pairNO'_apply' heiTrunc heiComm _ (n + m) v)
  have hCC : Function.HasFiniteSupport fun k : ℤ ↦
      (if n + m = 0 then ccTermInt (𝕜 := 𝕜) n k else 0) • v := by
    by_cases hnm : n + m = 0
    · simp only [hnm, if_true]
      exact (hasFiniteSupport_ccTermInt n).smul_left _
    · simp only [hnm, if_false, zero_smul]
      exact Function.hasFiniteSupport_fun_zero
  calc (sugawaraGen heiTrunc n).commutator (sugawaraGen heiTrunc m) v
      -- Expand `L m` as a sum of normal-ordered pairs.
      = (2 : 𝕜)⁻¹ • ∑ᶠ k, (sugawaraGen heiTrunc n).commutator (pairNO heiOper (m - k) k) v :=
        sugawaraGen_commutator_apply_eq_finsum_commutator_apply heiTrunc m _ v
      -- Commute `L n` past each normal-ordered pair.
    _ = (2 : 𝕜)⁻¹ • ∑ᶠ k : ℤ, ((-(k : 𝕜) • pairNO' heiOper (m - k) (n + k) v
          + -((m : 𝕜) - k) • pairNO' heiOper (n + m - k) k v)
          + (if n + m = 0 then ccTermInt (𝕜 := 𝕜) n k else 0) • v) := by
        refine congrArg _ (finsum_congr fun k ↦ ?_)
        rw [heiOper_pairNO_eq_pairNO' heiComm,
            commutator_sugawaraGen_heiPairNO' heiTrunc heiComm n m k]
        simp only [ccTermInt, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
      -- Separate the normal-ordered part from the central part.
    _ = (2 : 𝕜)⁻¹ • ((∑ᶠ k : ℤ, (-(k : 𝕜) • pairNO' heiOper (m - k) (n + k) v
          + -((m : 𝕜) - k) • pairNO' heiOper (n + m - k) k v))
          + ∑ᶠ k, (if n + m = 0 then ccTermInt (𝕜 := 𝕜) n k else 0) • v) := by
        rw [finsum_add_distrib hNO hCC]
      -- The normal-ordered part combines into `(n - m) • L (n+m)`.
    _ = ((n : 𝕜) - m) • sugawaraGen heiTrunc (n + m) v
          + (2 : 𝕜)⁻¹ • ∑ᶠ k, (if n + m = 0 then ccTermInt (𝕜 := 𝕜) n k else 0) • v := by
        rw [smul_add, sugawaraGen_NO_sum heiTrunc heiComm n m v]
        congr 1
        rw [smul_comm, sugawaraGen_apply]
        simp_rw [← heiOper_pairNO_eq_pairNO' heiComm]
      -- The central part evaluates to the central charge via `sugawaraGen_cc_sum`.
    _ = (((n : 𝕜) - m) • (sugawaraGen heiTrunc (n+m))
          + if n + m = 0 then (((n : 𝕜) ^ 3 - n) / 12) • (1 : V →ₗ[𝕜] V) else 0) v := by
        simp only [LinearMap.add_apply, LinearMap.smul_apply, DFunLike.ite_apply,
                   LinearMap.zero_apply, Module.End.one_apply]
        congr 1
        by_cases hnm : n + m = 0
        · simp only [hnm, if_true]
          rw [← finsum_smul' (hasFiniteSupport_ccTermInt n) v, sugawaraGen_cc_sum, smul_smul]
          congr 1
          ring
        · simp [hnm]

end normal_ordered_pair -- section



section representation

variable {heiOper}

open VirasoroAlgebra in
/-- Construct a representation of the Virasoro algebra from a central charge value `c` and a
collection `(Lₙ)`, `n ∈ ℤ`, of operators satisfying the commutation relations of Virasoro
generators with that central charge. -/
noncomputable def VirasoroAlgebra.representationOfCentralChargeOfL
    {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]
    {V : Type*} [AddCommGroup V] [Module 𝕂 V] (c : 𝕂) {lOper : ℤ → (V →ₗ[𝕂] V)}
    (lComm : ∀ n m, (lOper n).commutator (lOper m)
      = ((n : 𝕂) - m) • lOper (n+m)
        + if n + m = 0 then (c / 12 * ((n : 𝕂)^3 - n)) • (1 : V →ₗ[𝕂] V) else 0) :
    LieAlgebra.Representation 𝕂 𝕂 (VirasoroAlgebra 𝕂) V :=
  LieAlgebra.representationOfBasis (basisLC 𝕂) (genOper := fun i ↦ i.elim (c • 1) lOper) <| by
    intro i j
    match i, j with
    | none, j => simp
    | some n, none => simp
    | some n, some m =>
      simp only [Option.elim_some, basisLC_some, lgen_bracket, map_add, map_smul, lComm n m]
      congr 1
      · rw [show lgen 𝕂 (n + m) = (basisLC 𝕂) (some (n + m)) by simp,
            LieAlgebra.representationOfBasisAux_apply_basis]
        rfl
      · by_cases hnm : n + m = 0
        · simp only [hnm, if_true, map_smul,
                     show cgen 𝕂 = (basisLC 𝕂) none by simp,
                     LieAlgebra.representationOfBasisAux_apply_basis, Option.elim_none]
          rw [smul_smul]
          congr 1
          ring
        · simp [hnm]

@[simp] lemma VirasoroAlgebra.representationOfCentralChargeOfL_cgen
    {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]
    {V : Type*} [AddCommGroup V] [Module 𝕂 V] (c : 𝕂) {lOper : ℤ → (V →ₗ[𝕂] V)}
    (lComm : ∀ n m, (lOper n).commutator (lOper m)
      = ((n : 𝕂) - m) • lOper (n+m)
        + if n + m = 0 then (c / 12 * ((n : 𝕂)^3 - n)) • (1 : V →ₗ[𝕂] V) else 0) :
    (representationOfCentralChargeOfL c lComm) (cgen 𝕂) = c • 1 := by
  rw [show cgen 𝕂 = (basisLC 𝕂) none by simp]
  exact LieAlgebra.representationOfBasis_apply_basis (basisLC 𝕂) _ none

@[simp] lemma VirasoroAlgebra.representationOfCentralChargeOfL_lgen
    {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]
    {V : Type*} [AddCommGroup V] [Module 𝕂 V] (c : 𝕂) {lOper : ℤ → (V →ₗ[𝕂] V)}
    (lComm : ∀ n m, (lOper n).commutator (lOper m)
      = ((n : 𝕂) - m) • lOper (n+m)
        + if n + m = 0 then (c / 12 * ((n : 𝕂)^3 - n)) • (1 : V →ₗ[𝕂] V) else 0)
    (n : ℤ) :
    (representationOfCentralChargeOfL c lComm) (lgen 𝕂 n) = lOper n := by
  rw [show lgen 𝕂 n = (basisLC 𝕂) (some n) by simp]
  exact LieAlgebra.representationOfBasis_apply_basis (basisLC 𝕂) _ (some n)

include heiComm in
/-- The commutation relations of the Sugawara operators, in the normal form used by
`VirasoroAlgebra.representationOfCentralChargeOfL` (with central charge `c = 1`). -/
private lemma sugawaraGen_lComm [CharZero 𝕜] (n m : ℤ) :
    (sugawaraGen heiTrunc n).commutator (sugawaraGen heiTrunc m)
      = ((n : 𝕜) - m) • sugawaraGen heiTrunc (n+m)
        + if n + m = 0 then ((1 : 𝕜) / 12 * ((n : 𝕜)^3 - n)) • (1 : V →ₗ[𝕜] V) else 0 := by
  rw [commutator_sugawaraGen heiTrunc heiComm n m]
  congr 1
  split_ifs
  · congr 1
    ring
  · rfl

/-- **The basic bosonic Sugawara representation of Virasoro algebra (c=1)**:
On a vector space with a representation of the Heisenberg algebra that acts locally truncatedly,
we get a representation of the Virasoro algebra with central charge 1 by the Sugawara
construction. -/
noncomputable def sugawaraRepresentation [CharZero 𝕜] :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V) :=
  VirasoroAlgebra.representationOfCentralChargeOfL 1 (sugawaraGen_lComm heiTrunc heiComm)

open VirasoroAlgebra in
/-- The central element `C` of the Virasoro algebra acts as `1` on the representation obtained
by the basic bosonic Sugawara construction. -/
lemma sugawaraRepresentation_cgen [CharZero 𝕜] :
    sugawaraRepresentation heiTrunc heiComm (cgen 𝕜) = 1 := by
  have key :=
    VirasoroAlgebra.representationOfCentralChargeOfL_cgen 1 (sugawaraGen_lComm heiTrunc heiComm)
  rw [one_smul] at key
  exact key

open VirasoroAlgebra in
/-- The Virasoro generator `Lₙ` acts by the Sugawara operator `L n` on the representation
obtained by the basic bosonic Sugawara construction. -/
lemma sugawaraRepresentation_lgen [CharZero 𝕜] (n : ℤ) :
    sugawaraRepresentation heiTrunc heiComm (lgen 𝕜 n) = sugawaraGen heiTrunc n :=
  VirasoroAlgebra.representationOfCentralChargeOfL_lgen 1 (sugawaraGen_lComm heiTrunc heiComm) n

open VirasoroAlgebra in
/-- The formula for the action of the Virasoro generator `Lₙ` on the representation obtained
by the basic bosonic Sugawara construction. -/
lemma sugawaraRepresentation_lgen_apply' [CharZero 𝕜] (n : ℤ) (v : V) :
    sugawaraRepresentation heiTrunc heiComm (lgen 𝕜 n) v =
      (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO heiOper (n-k) k v := by
  rw [sugawaraRepresentation_lgen heiTrunc heiComm n, sugawaraGen_apply]

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
        (hasFiniteSupport_pairNO'_apply' heiTrunc heiComm n v)]
  congr 2
  · simp_rw [heiOper_pairNO'_symm heiComm]
    simp only [Set.mem_Ici, pairNO', ge_iff_le, LinearMap.coe_comp, Function.comp_apply]
    refine finsum_congr fun k ↦ ?_
    by_cases hk : 0 ≤ k <;> simp [hk]
  · simp_rw [heiOper_pairNO'_symm heiComm]
    simp only [Set.compl_Ici, Set.mem_Iio, pairNO', LinearMap.coe_comp, Function.comp_apply]
    refine finsum_congr fun k ↦ ?_
    by_cases hk : k < 0
    · simp [hk, show ¬ 0 ≤ k by omega]
    · simp [hk]

end representation

section heisenberg_representation

open HeisenbergAlgebra in
-- TODO: Generalize to `kgen` acting as `κ • 1`, maybe.
/-- **The basic bosonic Sugawara representation of Virasoro algebra (c=1)**:
On a vector space with a representation of the Heisenberg algebra that acts locally truncatedly
(and the central element `k` acts as `1`), we get a representation of the Virasoro algebra with
central charge `c = 1` by the Sugawara construction. -/
noncomputable def sugawaraRepresentation_of_representation_heisenbergAlgebra [CharZero 𝕜]
    (α : LieAlgebra.Representation 𝕜 𝕜 (HeisenbergAlgebra 𝕜) V)
    (hα : ∀ v, ∀ᶠ k in atTop, α (jgen _ k) v = 0) (hαc : α (kgen _) = 1) :
    LieAlgebra.Representation 𝕜 𝕜 (VirasoroAlgebra 𝕜) V :=
  sugawaraRepresentation hα <| by
    intro k l
    simp [← LieAlgebra.Representation.apply_bracket_eq_commutator α (jgen _ k) (jgen _ l)]
    by_cases hkl : k + l = 0
    · simp [hkl, hαc]
    · simp [hkl]

end heisenberg_representation

end Sugawara_boson -- section

end VirasoroProject -- namespace
