/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import VirasoroProject.VirasoroAlgebra
import Mathlib

/-!
# The bosonic Sugawara construction
-/

namespace VirasoroProject

section Sugawara_boson

open Filter

variable {𝕜 : Type*} [Field 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- Commutator `[A,B] := AB-BA` of two linear operators `A`, `B`. -/
def commutator (A B : V →ₗ[𝕜] V) : V →ₗ[𝕜] V := A * B - B * A

/-- `[A,B] = -[B,A]` -/
lemma commutator_comm (A B : V →ₗ[𝕜] V) :
    commutator A B = - commutator B A := by
  simp [commutator]

lemma mul_eq_mul_add_commutator (A B : V →ₗ[𝕜] V) :
    A * B = B * A + commutator A B := by
  simp [commutator]

/-- `[AB,C] = A[B,C] + [A,C]B` -/
lemma commutator_pair (A B C : V →ₗ[𝕜] V) :
    commutator (A * B) C = A * (commutator B C) + (commutator A C) * B := by
  simp [commutator, sub_mul, mul_sub, ← mul_assoc]

/-- `[A,BC] = B[A,C] + [A,B]C` -/
lemma commutator_pair' (A B C : V →ₗ[𝕜] V) :
    commutator A (B * C) = B * (commutator A C) + (commutator A B) * C := by
  simp [commutator, sub_mul, mul_sub, ← mul_assoc]

variable (heiOper : ℤ → (V →ₗ[𝕜] V))
variable (heiTrunc : ∀ v, atTop.Eventually (fun l ↦ (heiOper l) v = 0))
variable (heiComm : ∀ k l,
  commutator (heiOper k) (heiOper l) = if k + l = 0 then (k : 𝕜) • 1 else 0)

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
  simpa [hkl, sub_eq_zero, commutator] using heiComm k l

/-- The two definitions of normal ordered pairs coincide. -/
lemma heiOper_pairNO_eq_pairNO' (k l : ℤ) :
    pairNO heiOper k l = pairNO' heiOper k l := by
  unfold pairNO pairNO'
  by_cases hk : 0 ≤ k
  · simp only [hk, ↓reduceIte, ite_eq_left_iff, not_le]
    intro hkl
    apply heiComm_of_add_ne_zero _ heiComm
    exact ne_of_gt (by linarith)
  · simp only [hk, ↓reduceIte, ite_eq_right_iff]
    intro hlk
    apply heiComm_of_add_ne_zero _ heiComm
    exact ne_of_lt (by linarith)

include heiTrunc in
lemma finite_support_pairNO_heiOper_apply (n m : ℤ) (v : V) :
    (Function.support fun k => ((pairNO heiOper (m - k) (n + k)) v)).Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp <| heiTrunc v
  apply (Set.finite_Ioo (m - N) (N - n)).subset
  simp only [Function.support_subset_iff, ne_eq, Set.mem_Icc, tsub_le_iff_right]
  intro k hk
  by_contra con
  apply hk
  apply pairNO_apply_eq_zero _ hN
  by_cases h : N ≤ n + k
  · exact le_sup_of_le_right h
  · apply le_sup_of_le_left
    simp only [Set.mem_Ioo, not_and, not_lt, tsub_le_iff_right] at con
    by_contra con'
    specialize con (by linarith)
    linarith

include heiTrunc in
lemma finite_support_pairNO'_heiOper_apply (n m : ℤ) (v : V) :
    (Function.support fun k => ((pairNO' heiOper (m - k) (n + k)) v)).Finite := by
  apply (finite_support_pairNO_heiOper_apply _ heiTrunc heiComm n m v).subset
  intro j hj
  convert hj using 2
  funext k
  rw [heiOper_pairNO_eq_pairNO' _ heiComm]

omit heiComm

/-- `pairNO k l` is symmetric in `k` and `l`. -/
lemma heiOper_pairNO_symm (k l : ℤ) :
    pairNO heiOper k l = pairNO heiOper l k := by
  unfold pairNO
  by_cases heq : l = k
  · rw [heq]
  by_cases hlk : l ≤ k
  · have hkl : ¬ k ≤ l := by linarith [lt_of_le_of_ne hlk heq]
    simp [hlk, hkl]
  · have hkl : k ≤ l := by linarith
    simp [hlk, hkl]

include heiComm

lemma heiOper_pairNO'_symm (k l : ℤ) :
    pairNO' heiOper k l = pairNO' heiOper l k := by
  simpa [← heiOper_pairNO_eq_pairNO' _ heiComm] using heiOper_pairNO_symm heiOper k l

omit heiComm
include heiTrunc

-- Maybe this one is not the most useful; want to fix the sum of indices.
lemma heiPairNO_trunc (k : ℤ) (v : V) :
    atTop.Eventually (fun l ↦ pairNO heiOper k l v = 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (heiTrunc v)
  filter_upwards [Ici_mem_atTop N] with l hl
  rw [Set.mem_Ici] at hl
  by_cases hlk : l ≤ k
  · simp [pairNO, hlk, hN _ (show N ≤ k by linarith)]
  · simp [pairNO, hlk, hN _ hl]

lemma heiPairNO_trunc_atTop_sub (n : ℤ) (v : V) :
    atTop.Eventually (fun k ↦ pairNO heiOper (n-k) k v = 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (heiTrunc v)
  filter_upwards [Ici_mem_atTop N] with l hl
  rw [Set.mem_Ici] at hl
  by_cases hln : l ≤ n-l
  · simp [pairNO, hln, hN _ (show N ≤ n-l by linarith)]
  · simp [pairNO, hln, hN _ (show N ≤ l by linarith)]

lemma heiPairNO_trunc_atBot_sub (n : ℤ) (v : V) :
    atBot.Eventually (fun k ↦ pairNO heiOper (n-k) k v = 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (heiTrunc v)
  filter_upwards [Iic_mem_atBot (n-N)] with l hl
  rw [Set.mem_Iic] at hl
  by_cases hln : l ≤ n-l
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
  · exact hT k (hkBT (Int.lt_of_not_ge hk))

#check tsum
#check discreteTopology_bot

open Topology

#check Finset.insert_comm

omit heiTrunc in
lemma DiscreteTopology.summable_iff_eventually_zero
    {E : Type*} [AddCommGroup E] [TopologicalSpace E] [DiscreteTopology E]
    {ι : Type*} [DecidableEq ι] (f : ι → E) :
    Summable f ↔ cofinite.Eventually (fun n ↦ f n = 0) := by
  constructor
  · intro ⟨v, hv⟩
    obtain ⟨s, hs⟩ := mem_atTop_sets.mp <|
      tendsto_iff_forall_eventually_mem.mp hv _ (show {v} ∈ 𝓝 v from mem_nhds_discrete.mpr rfl)
    rw [eventually_cofinite]
    apply s.finite_toSet.subset
    intro i (hi : f i ≠ 0)
    by_contra con
    apply hi
    have obs : ∑ b ∈ insert i s, f b = v := hs (insert i s) (by simp)
    simpa [Finset.sum_insert con, show ∑ b ∈ s, f b = v from hs s le_rfl, add_eq_right] using obs
  · intro ev_zero
    exact summable_of_finite_support ev_zero

variable {heiOper} in
lemma sugawaraGenAux_summable (n : ℤ) (v : V) :
    @Summable V ℤ _ ⊥ (fun k ↦ pairNO heiOper (n-k) k v) := by
  let tV : TopologicalSpace V := ⊥
  apply summable_of_finite_support
  exact heiPairNO_trunc_cofinite_sub heiOper heiTrunc n v

variable {heiOper} in
lemma comp_sugawaraGenAux_summable (A : V →ₗ[𝕜] V) (n : ℤ) (v : V) :
    @Summable V ℤ _ ⊥ (fun k ↦ A (pairNO heiOper (n-k) k v)) := by
  let tV : TopologicalSpace V := ⊥
  apply summable_of_finite_support
  apply (heiPairNO_trunc_cofinite_sub heiOper heiTrunc n v).subset
  intro i hi
  simp only [Function.mem_support, ne_eq, Set.mem_compl_iff, Set.mem_setOf_eq] at hi ⊢
  intro con
  simp [con] at hi

noncomputable def sugawaraGenAux (n : ℤ) (v : V) : V :=
  (2 : 𝕜)⁻¹ • @tsum V _ ⊥ ℤ (fun k ↦ pairNO heiOper (n-k) k v)

omit heiTrunc in
lemma sugawaraGenAux_def (n : ℤ) (v : V) :
    sugawaraGenAux heiOper n v = (2 : 𝕜)⁻¹ • @tsum V _ ⊥ ℤ (fun k ↦ pairNO heiOper (n-k) k v) :=
  rfl

omit heiTrunc in
lemma sugawaraGenAux_comp_apply (A : V →ₗ[𝕜] V) (n : ℤ) (v : V) :
    (sugawaraGenAux heiOper n (A v))
      = (2 : 𝕜)⁻¹ • @tsum V _ ⊥ ℤ (fun k ↦ (pairNO heiOper (n-k) k (A v))) := by
  rw [sugawaraGenAux_def heiOper n (A v)]

variable {heiOper} in
lemma comp_sugawaraGenAux_apply (A : V →ₗ[𝕜] V) (n : ℤ) (v : V) :
    A (sugawaraGenAux heiOper n v)
      = (2 : 𝕜)⁻¹ • @tsum V _ ⊥ ℤ (fun k ↦ A (pairNO heiOper (n-k) k v)) := by
  let tV : TopologicalSpace V := ⊥
  have V_discr : DiscreteTopology V := forall_open_iff_discrete.mp fun _ ↦ trivial
  rw [sugawaraGenAux_def heiOper n v, map_smul]
  congr 1
  refine Summable.map_tsum ?_ A ⟨fun _ h ↦ h⟩
  exact sugawaraGenAux_summable heiTrunc n v

omit heiTrunc

example {X : Type*} [TopologicalSpace X] [DiscreteTopology X] :
    T2Space X := by
  exact DiscreteTopology.toT2Space

example {X : Type*} [TopologicalSpace X] [DiscreteTopology X] [AddCommMonoid X] :
    ContinuousAdd X := by
  exact continuousAdd_of_discreteTopology

lemma continuousConstSMul_of_discreteTopology (𝕜 X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] [AddCommMonoid X] [SMul 𝕜 X] :
    ContinuousConstSMul 𝕜 X :=
  ⟨fun c ↦ by continuity⟩

variable {heiOper}

include heiTrunc

lemma sugawaraGenAux_add (n : ℤ) (v w : V) :
    sugawaraGenAux heiOper n (v + w) = sugawaraGenAux heiOper n v + sugawaraGenAux heiOper n w := by
  let tV : TopologicalSpace V := ⊥
  have V_discr : DiscreteTopology V := forall_open_iff_discrete.mp fun _ ↦ trivial
  --have V_T2 : T2Space V := DiscreteTopology.toT2Space
  simp only [sugawaraGenAux_def, map_add, ← smul_add]
  congr 1
  rw [Summable.tsum_add]
  · exact sugawaraGenAux_summable heiTrunc n v
  · exact sugawaraGenAux_summable heiTrunc n w

lemma sugawaraGenAux_smul (n : ℤ) (c : 𝕜) (v : V) :
    sugawaraGenAux heiOper n (c • v) = c • sugawaraGenAux heiOper n v := by
  let tV : TopologicalSpace V := ⊥
  have V_discr : DiscreteTopology V := forall_open_iff_discrete.mp fun _ ↦ trivial
  have V_smul_cont := continuousConstSMul_of_discreteTopology 𝕜 V
  simp [sugawaraGenAux_def]
  rw [Summable.tsum_const_smul, smul_comm]
  exact sugawaraGenAux_summable heiTrunc n v

noncomputable def sugawaraGen (n : ℤ) : V →ₗ[𝕜] V where
  toFun := sugawaraGenAux heiOper n
  map_add' v w := sugawaraGenAux_add heiTrunc n v w
  map_smul' c v := sugawaraGenAux_smul heiTrunc n c v

lemma sugawaraGen_apply (n : ℤ) (v : V) :
    sugawaraGen heiTrunc n v = (2 : 𝕜)⁻¹ • @tsum V _ ⊥ ℤ (fun k ↦ pairNO heiOper (n-k) k v) :=
  rfl

example {ι E : Type*} [AddCommMonoid E] [TopologicalSpace E] (f : ι → E) (σ : ι ≃ ι) :
    ∑' i, f (σ i) = ∑' i, f i := by
  exact Equiv.tsum_eq σ f

lemma sugawaraGen_apply_eq_tsum_shift (n s : ℤ) (v : V) :
    sugawaraGen heiTrunc n v
      = (2 : 𝕜)⁻¹ • @tsum V _ ⊥ ℤ (fun k ↦ pairNO heiOper (n - (k + s)) (k + s) v) := by
  rw [sugawaraGen_apply]
  congr 1
  let σ : ℤ ≃ ℤ := ⟨fun n ↦ n + s, fun n ↦ n - s, fun n ↦ by simp, fun n ↦ by simp⟩
  let tV : TopologicalSpace V := ⊥
  rw [← σ.tsum_eq]
  simp [σ]

lemma commutator_sugawaraGen_apply_eq_tsum_commutator_apply (n : ℤ) (A : V →ₗ[𝕜] V) (v : V) :
    commutator (sugawaraGen heiTrunc n) A v =
      (2 : 𝕜)⁻¹ • @tsum V _ ⊥ ℤ (fun k ↦ commutator (pairNO heiOper (n-k) k) A v) := by
  let tV : TopologicalSpace V := ⊥
  have V_discr : DiscreteTopology V := forall_open_iff_discrete.mp fun _ ↦ trivial
  have V_smul_cont := continuousConstSMul_of_discreteTopology 𝕜 V
  simp only [commutator, LinearMap.sub_apply, Module.End.mul_apply]
  simp_rw [sub_eq_add_neg]
  rw [Summable.tsum_add]
  · rw [smul_add]
    congr
    convert comp_sugawaraGenAux_apply heiTrunc (-A) n v using 1
  · exact sugawaraGenAux_summable heiTrunc n (A v)
  · convert comp_sugawaraGenAux_summable heiTrunc (-A) n v using 1

lemma sugawaraGen_commutator_apply_eq_tsum_commutator_apply (n : ℤ) (A : V →ₗ[𝕜] V) (v : V) :
    commutator A (sugawaraGen heiTrunc n) v =
      (2 : 𝕜)⁻¹ • @tsum V _ ⊥ ℤ (fun k ↦ commutator A (pairNO heiOper (n-k) k) v) := by
  let tV : TopologicalSpace V := ⊥
  have V_discr : DiscreteTopology V := forall_open_iff_discrete.mp fun _ ↦ trivial
  have V_tag : IsTopologicalAddGroup V :=
    { toContinuousAdd := continuousAdd_of_discreteTopology,
      toContinuousNeg := continuousNeg_of_discreteTopology }
  rw [commutator_comm, LinearMap.neg_apply]
  rw [commutator_sugawaraGen_apply_eq_tsum_commutator_apply]
  rw [← smul_neg, ← tsum_neg]
  congr 2
  funext j
  rw [commutator_comm, LinearMap.neg_apply, neg_neg]

omit heiTrunc

include heiComm

/-- `[(heiOper l) ∘ (heiOper k), (heiOper m)] = -m * (δ[k+m=0] + δ[l+m=0]) • heiOper (k + l + m)` -/
lemma commutator_heiPair_heiGen (l k m : ℤ) :
    commutator ((heiOper l) * (heiOper k)) (heiOper m)
      = ((-m : 𝕜) * ((if k + m = 0 then 1 else 0)
               + (if l + m = 0 then 1 else 0))) • heiOper (k + l + m) := by
  simp [commutator_pair, heiComm]
  by_cases hkm : k + m = 0
  · have k_eq : k = -m := by linarith
    simp [k_eq]
    by_cases hlm : l + m = 0
    · have l_eq : l = -m := by linarith
      simp [l_eq, mul_add, add_smul]
    · simp [hlm]
  · simp [hkm]
    by_cases hlm : l + m = 0
    · have l_eq : l = -m := by linarith
      simp [l_eq]
    · simp [hlm]

/-- `[:(heiOper l)(heiOper k):, (heiOper m)] = -m * (δ[k+m=0] + δ[l+m=0]) • heiOper (k + l + m)` -/
lemma commutator_heiPairNO_heiGen (l k m : ℤ) :
    commutator (pairNO heiOper l k) (heiOper m)
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
    commutator (sugawaraGen heiTrunc n) (heiOper m) = -m • heiOper (n + m) := by
  ext v
  rw [commutator_sugawaraGen_apply_eq_tsum_commutator_apply]
  simp_rw [commutator_heiPairNO_heiGen heiComm]
  simp only [neg_mul, add_sub_cancel, neg_smul, LinearMap.neg_apply, LinearMap.smul_apply,
             zsmul_eq_mul, Module.End.mul_apply, Module.End.intCast_apply]
  let tV : TopologicalSpace V := ⊥
  have V_discr : DiscreteTopology V := forall_open_iff_discrete.mp fun _ ↦ trivial
  have V_smul_cont := continuousConstSMul_of_discreteTopology 𝕜 V
  have V_tag : IsTopologicalAddGroup V :=
    { toContinuousAdd := continuousAdd_of_discreteTopology,
      toContinuousNeg := continuousNeg_of_discreteTopology }
  simp only [mul_add, mul_ite, mul_one, mul_zero, add_smul, ite_smul, zero_smul]
  rw [tsum_neg, Summable.tsum_add]
  · rw [@tsum_eq_single V ℤ _ ⊥ _ (-m)]
    · simp only [neg_add_cancel, ↓reduceIte]
      rw [tsum_eq_single (n + m)]
      · simp only [sub_add_cancel_left, neg_add_cancel, ↓reduceIte]
        simp only [← two_smul (R := 𝕜), ← smul_assoc, smul_eq_mul, smul_neg, ← mul_assoc, neg_inj]
        simp [inv_mul_cancel₀ (G₀ := 𝕜) two_ne_zero, one_mul]
        norm_cast
      · intro j hjnm
        simp [show n - j + m ≠ 0 by intro con ; apply hjnm ; linarith]
    · intro j hjm
      simp [show j + m ≠ 0 by intro con ; apply hjm ; linarith]
  · apply summable_of_finite_support
    apply (show Set.Finite {-m} from Set.finite_singleton (-m)).subset
    simp only [Set.subset_singleton_iff, Function.mem_support, ne_eq, ite_eq_right_iff,
               smul_eq_zero, Classical.not_imp, not_or, and_imp]
    intro j hjm _ _
    linarith
  · apply summable_of_finite_support
    apply (show Set.Finite {n + m} from Set.finite_singleton (n + m)).subset
    simp only [Set.subset_singleton_iff, Function.mem_support, ne_eq, ite_eq_right_iff,
               smul_eq_zero, Classical.not_imp, not_or, and_imp]
    intro j hjm _ _
    linarith

/-- `[L(n), J(m-k)J(k)] = -k • J(m-k)J(n+k) - (m-k) • J(n+m-k)J(k)` -/
lemma commutator_sugawaraGen_heiOperPair [CharZero 𝕜] (n m k : ℤ) :
    commutator (sugawaraGen heiTrunc n) (heiOper (m-k) * heiOper k)
      = -k • (heiOper (m-k) * heiOper (n+k)) - (m-k) • (heiOper (n+m-k) * heiOper k) := by
  rw [commutator_pair']
  rw [commutator_sugawaraGen_heiOper _ heiComm, commutator_sugawaraGen_heiOper _ heiComm]
  simp only [neg_smul, zsmul_eq_mul, mul_neg, neg_sub, Int.cast_sub, sub_eq_add_neg]
  congr 2
  · simp only [← mul_assoc]
    congr 1
    exact (Int.cast_comm k _).symm
  · simp [show n + (m + -k) = n + m + -k by ring, ← mul_assoc]

/-- `[L(n), :J(m-k)J(k):] = -k • :J(m-k)J(n+k): - (m-k) • :J(n+m-k)J(k): + extra terms • 1` -/
lemma commutator_sugawaraGen_heiPairNO' [CharZero 𝕜] (n m k : ℤ) :
    commutator (sugawaraGen heiTrunc n) (pairNO' heiOper k (m-k))
      = -k • (pairNO' heiOper (n+k) (m-k)
        + if 0 ≤ k ∧ k < -n ∧ n + m = 0 then -(n + k) • 1 else 0
        + if k < 0 ∧ -n ≤ k ∧ n + m = 0 then (n + k) • 1 else 0)
        - (m-k) • (pairNO' heiOper k (n+m-k)) := by
  by_cases hk : 0 ≤ k
  · by_cases hnk : 0 ≤ n + k
    · have hk' : ¬ k < 0 := by linarith
      have hnk' : ¬ k < -n := by linarith
      simp only [pairNO', hk, hk', hnk, hnk', ↓reduceIte, and_false, true_and, false_and, add_zero,
                 neg_smul, zsmul_eq_mul, Int.cast_sub, ← Module.End.mul_eq_comp]
      simp [commutator_sugawaraGen_heiOperPair heiTrunc heiComm]
    · have hnk' : k < -n := by linarith
      simp only [pairNO', hk, ↓reduceIte, hnk, hnk', and_true, add_zero, neg_smul, zsmul_eq_mul,
                 Int.cast_sub, ← Module.End.mul_eq_comp]
      rw [commutator_sugawaraGen_heiOperPair heiTrunc heiComm]
      have aux := (heiComm (n+k) (m-k)) ▸ mul_eq_mul_add_commutator (heiOper (n+k)) (heiOper (m-k))
      simp only [aux, show n + k + (m - k) = n + m by ring, neg_smul, zsmul_eq_mul, Int.cast_sub,
                 Int.cast_add, true_and, Int.cast_ite, Int.cast_zero, sub_left_inj, neg_inj]
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
      simp only [pairNO', hk, hk', hnk, hnk', ↓reduceIte, and_false, true_and, false_and, add_zero,
                 neg_smul, zsmul_eq_mul, Int.cast_sub, ← Module.End.mul_eq_comp]
      simp only [obs, add_sub, Int.cast_add, mul_one, neg_add_rev, zero_add]
      have aux := (heiComm (m-k) (n+k)) ▸ mul_eq_mul_add_commutator (heiOper (m-k)) (heiOper (n+k))
      rw [aux, show m - k + (n + k) = n + m by ring]
      rw [sub_eq_add_neg _ ((k : V →ₗ[𝕜] V) * _), sub_eq_add_neg _ ((m - k : V →ₗ[𝕜] V) * _)]
      rw [add_comm _ (-_)]
      simp only [Int.cast_add, mul_one, neg_add_rev, zero_add, neg_add, ← neg_mul]
      simp only [mul_add (_ : V →ₗ[𝕜] V), add_assoc, add_right_inj, add_sub]
      by_cases hnm : n + m = 0
      · simp only [hnm, zero_sub, ↓reduceIte, Int.cast_sub, Algebra.mul_smul_comm, mul_one,
                   smul_neg, neg_mul, neg_sub]
        rw [show n = -m by linarith]
        simp only [right_eq_add, sub_eq_add_neg, add_smul, mul_add, ← add_assoc,
                   neg_add, mul_neg, neg_smul, neg_neg]
        have (j : ℤ) : Int.cast (R := V →ₗ[𝕜] V) j = Int.cast (R := 𝕜) j • 1 := by norm_cast
        simp [this]
      · simp [hnm]
    · have hk' : k < 0 := by linarith
      have hnk' : ¬ -n ≤ k := by linarith
      simp only [pairNO', hk, hk', hnk, hnk', ↓reduceIte, and_false, true_and, false_and, add_zero,
                 neg_smul, zsmul_eq_mul, Int.cast_sub, ← Module.End.mul_eq_comp]
      rw [obs]
      rw [sub_eq_add_neg _ ((k : V →ₗ[𝕜] V) * _), sub_eq_add_neg _ ((m - k : V →ₗ[𝕜] V) * _)]
      rw [add_comm _ (-_)]
      simp only [Int.cast_add, mul_one, neg_add_rev, zero_add, neg_add, ← neg_mul]
      simp only [mul_add (_ : V →ₗ[𝕜] V), add_assoc, add_right_inj, add_sub]
      congr 1
      simp

/-- `[L(n), :J(m-k)J(k):] v = -k • :J(m-k)J(n+k): v - (m-k) • :J(n+m-k)J(k): v + extra terms • v` -/
lemma commutator_sugawaraGen_heiPairNO'_apply [CharZero 𝕜] (n m k : ℤ) (v : V) :
    commutator (sugawaraGen heiTrunc n) (pairNO' heiOper k (m-k)) v
      = -k • ((pairNO' heiOper (n+k) (m-k) v)
        + if 0 ≤ k ∧ k < -n ∧ n + m = 0 then -(n + k) • v else 0
        + if k < 0 ∧ -n ≤ k ∧ n + m = 0 then (n + k) • v else 0)
        - (m-k) • (pairNO' heiOper k (n+m-k) v) := by
  have key := LinearMap.congr_fun (commutator_sugawaraGen_heiPairNO' heiTrunc heiComm n m k) v
  simp only [LinearMap.sub_apply, LinearMap.add_apply] at key
  rw [key]
  simp_rw [smul_add, sub_eq_add_neg, neg_add, LinearMap.add_apply, LinearMap.smul_apply, add_assoc]
  rw [add_right_inj]
  simp only [← add_assoc]
  rw [add_left_inj]
  split_ifs <;> simp [add_smul]

/-- `[L(n), L(m)] = (n-m) • L(n+m) + extra terms • 1` -/
lemma commutator_sugawaraGen [CharZero 𝕜] (n m : ℤ) :
    commutator (sugawaraGen heiTrunc n) (sugawaraGen heiTrunc m)
      = (n-m) • (sugawaraGen heiTrunc (n+m))
        + if n + m = 0 then ((n ^ 3 - n : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V) else 0 := by
  let tV : TopologicalSpace V := ⊥
  have V_discr : DiscreteTopology V := forall_open_iff_discrete.mp fun _ ↦ trivial
  have V_smul_cont := continuousConstSMul_of_discreteTopology 𝕜 V
  have V_tag : IsTopologicalAddGroup V :=
    { toContinuousAdd := continuousAdd_of_discreteTopology,
      toContinuousNeg := continuousNeg_of_discreteTopology }
  ext v
  rw [sugawaraGen_commutator_apply_eq_tsum_commutator_apply]
  simp only [heiOper_pairNO_eq_pairNO' heiOper heiComm]
  --simp only [commutator_sugawaraGen_heiPairNO'_apply heiTrunc heiComm ]
  have (k : ℤ) := commutator_sugawaraGen_heiPairNO'_apply heiTrunc heiComm n m (m-k) v
  simp only [show ∀ k, m - (m-k) = k by intro k; ring] at this
  simp_rw [this, sub_eq_add_neg, smul_add, ← add_assoc]
  rw [Summable.tsum_add]
  · simp only [neg_add_rev, neg_neg, le_add_neg_iff_add_le, zero_add, add_neg_lt_iff_lt_add,
        lt_neg_add_iff_add_lt, neg_add_le_iff_le_add, smul_ite, smul_zero, smul_add, zsmul_eq_mul,
        Int.cast_add, Int.cast_neg, LinearMap.add_apply, Module.End.mul_apply,
        Module.End.intCast_apply, LinearMap.neg_apply]
    rw [Summable.tsum_add]
    · --simp only [smul_add]

      sorry
    · sorry
    · sorry
  · apply summable_of_finite_support
    sorry
  · apply summable_of_finite_support
    apply (finite_support_pairNO'_heiOper_apply heiOper heiTrunc heiComm n m v).subset
    intro k hk
    simp only [neg_add_rev, neg_neg, Function.support_neg, Function.mem_support, ne_eq] at hk ⊢
    intro con
    apply hk
    simp [← sub_eq_add_neg, con]

end normal_ordered_pair -- section

section central_charge_calculation

open Finset

/-- A discrete integral of a function on `ℕ`. -/
def nPrimitive {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) : R := match n with
  | 0 => (0 : R)
  | n + 1 => nPrimitive f n + f n

@[simp] lemma nPrimitive_zero {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    nPrimitive f 0 = 0 :=
  rfl

@[simp] lemma nPrimitive_succ {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    nPrimitive f (n + 1) = nPrimitive f n + f n :=
  rfl

lemma nPrimitive_eq_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    nPrimitive f n = ∑ j in range n, f j := by
  induction' n with n ih
  · simp
  · simp [nPrimitive_succ, sum_range_succ, ih]

/-- A discrete integral of a function on `ℤ`. -/
def zPrimitive {R : Type*} [AddCommGroup R] (f : ℤ → R) (n : ℤ) : R :=
  if 0 ≤ n then ∑ j in range (Int.toNat n), f j else -(∑ j in range (Int.natAbs n), f (-j-1))

@[simp] lemma zPrimitive_zero {R : Type*} [AddCommGroup R] (f : ℤ → R) :
    zPrimitive f 0 = 0 :=
  rfl

@[simp] lemma zPrimitive_apply_of_nonneg {R : Type*} [AddCommGroup R] (f : ℤ → R)
    {n : ℤ} (hn : 0 ≤ n) :
    zPrimitive f n = ∑ j in range (Int.toNat n), f j := by
  simp [zPrimitive, hn]

@[simp] lemma zPrimitive_apply_of_nonpos {R : Type*} [AddCommGroup R] (f : ℤ → R)
    {n : ℤ} (hn : n ≤ 0) :
    zPrimitive f n = -(∑ j in range (Int.natAbs n), f (-j-1)) := by
  by_cases hn' : n = 0
  · simp [hn']
  · simp [zPrimitive, lt_of_le_of_ne hn hn']

@[simp] lemma zPrimitive_succ {R : Type*} [AddCommGroup R] (f : ℤ → R) (n : ℤ) :
    zPrimitive f (n + 1) = zPrimitive f n + f n := by
  by_cases hn : 0 ≤ n
  · simp [zPrimitive, hn, Int.le_add_one hn, Int.toNat_add hn zero_le_one, sum_range_succ]
  · simp only [not_le] at hn
    have n_natAbs : n.natAbs = (n+1).natAbs + 1 := by
      simpa using Int.natAbs_add_of_nonpos (b := -1) hn (Int.toNat_eq_zero.mp rfl)
    simp only [zPrimitive_apply_of_nonpos _ hn, zPrimitive_apply_of_nonpos _ hn.le, n_natAbs,
               sum_range_succ, Int.natCast_natAbs, neg_add_rev]
    simp only [add_comm (-(f _)), add_assoc, left_eq_add]
    simp [show -|n + 1| - 1 = n by rw [abs_of_nonpos hn, neg_neg] ; ring]

lemma eq_zPrimitive_of_eq_zero_of_forall_eq_add {R : Type*} [AddCommGroup R] {f F : ℤ → R}
    (h0 : F 0 = 0) (h1 : ∀ n, F (n + 1) = F n + f n) :
    F = zPrimitive f := by
  have obsP : ∀ (n : ℕ), F n = zPrimitive f n := by
    intro n
    induction' n with n ih
    · simp [h0]
    · have keyF := h1 n
      have keyP := zPrimitive_succ f n
      norm_cast at *
      rw [keyF, ih, ← keyP]
  have obsM : ∀ (n : ℕ), F (-n) = zPrimitive f (-n) := by
    intro n
    induction' n with n ih
    · simp [h0]
    · have keyF := h1 (-(n + 1))
      have keyP := zPrimitive_succ f (-(n + 1))
      simp only [Int.natAbs_neg, Int.natAbs_natCast, neg_add_rev, Int.reduceNeg,
                 neg_add_cancel_comm, Nat.cast_add, Nat.cast_one] at ih keyF keyP ⊢
      rw [keyF, keyP] at ih
      exact add_right_cancel_iff.mp ih
  ext m
  by_cases hm : 0 ≤ m
  · rw [(Int.toNat_of_nonneg hm).symm]
    exact obsP m.toNat
  · have hm' : m < 0 := Int.lt_of_not_ge hm
    rw [show m = -m.natAbs from Int.eq_neg_comm.mp (by simpa [hm'] using hm'.le)]
    exact obsM m.natAbs

lemma zPrimitive_add {R : Type*} [AddCommGroup R] (f g : ℤ → R) :
    zPrimitive (f + g) = zPrimitive f + zPrimitive g  := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp only [Pi.add_apply, zPrimitive_succ]
    ac_rfl

lemma zPrimitive_smul {R S : Type*} [AddCommGroup R] [DistribSMul S R]
    (c : S) (f : ℤ → R) :
    zPrimitive (c • f) = c • (zPrimitive f) := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm <;> simp

lemma zPrimitive_sub {R : Type*} [AddCommGroup R] (f g : ℤ → R) :
    zPrimitive (f - g) = zPrimitive f - zPrimitive g  := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp only [Pi.sub_apply, zPrimitive_succ, ←sub_sub, sub_eq_add_neg, neg_add_rev, ←add_assoc]
    ac_rfl

lemma zPrimitive_mul_left {R : Type*} [Ring R] (c : R) (f : ℤ → R) :
    zPrimitive (fun n ↦ c * f n) = fun n ↦ c * zPrimitive f n := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp [mul_add]

lemma zPrimitive_mul_right {R : Type*} [Ring R] (c : R) (f : ℤ → R) :
    zPrimitive (fun n ↦ f n * c) = fun n ↦ zPrimitive f n * c := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp [add_mul]

def zMonomialF (R : Type*) [AddCommGroup R] [One R] (d : ℕ) : ℤ → R := match d with
  | 0 => fun _ ↦ 1
  | d + 1 => zPrimitive (zMonomialF R d)

lemma zMonomialF_eq (R : Type) [Field R] [CharZero R] (d : ℕ) :
    (zMonomialF R d) = (fun (n : ℤ) ↦ ((∏ j in range d, (n - j : R)) / (Nat.factorial d : R))) := by
  induction' d with d ihd
  · funext n
    simp [zMonomialF]
  rw [zMonomialF, Eq.comm]
  apply eq_zPrimitive_of_eq_zero_of_forall_eq_add
  · simp only [Int.cast_zero, zero_sub, prod_div_distrib, prod_const, card_range, div_eq_zero_iff,
               ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
               pow_eq_zero_iff, Nat.cast_eq_zero]
    left
    exact prod_eq_zero_iff.mpr ⟨0, by simp, by simp⟩
  · intro n
    simp only [Int.cast_add, Int.cast_one] at *
    simp [ihd]
    rw [prod_range_succ, prod_range_succ]
    --have := Nat.factorial_ne_zero d
    --have := Nat.factorial_ne_zero (d + 1)
    sorry

lemma zMonomialF_zero_eq (R : Type) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 0 n = 1 := by
  simp [zMonomialF]

lemma zMonomialF_one_eq (R : Type) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 1 n = n := by
  simp [zMonomialF_eq]

lemma zMonomialF_two_eq (R : Type) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 2 n = n * (n - 1) / 2 := by
  simp [zMonomialF_eq, prod_range_succ]

lemma zMonomialF_three_eq (R : Type) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 3 n = n * (n - 1) * (n - 2) / 6 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 3 = 6 from rfl]

lemma zMonomialF_four_eq (R : Type) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 4 n = n * (n - 1) * (n - 2) * (n - 3) / 24 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 4 = 24 from rfl]

lemma zMonomialF_five_eq (R : Type) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 5 n = n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 5 = 120 from rfl]

lemma zMonomialF_apply_eq_zero_of_of_nonneg_lt (R : Type) [Field R] [CharZero R]
    (d : ℕ) {n : ℕ} (n_lt : n < d) :
    zMonomialF R d n = 0 := by
  simp only [zMonomialF_eq R d, Int.cast_natCast, div_eq_zero_iff, Nat.cast_eq_zero]
  exact Or.inl <| prod_eq_zero_iff.mpr ⟨n, ⟨mem_range.mpr n_lt, by simp⟩⟩

lemma bosonic_sugawara_cc_calc (n : ℤ) :
    zPrimitive (fun l ↦ (l : ℚ) * (n - l)) n = (n^3 - n) / 6 := by
  have obs : (n^3 - n) / 6 = (n - 1 : ℚ) * zMonomialF ℚ 2 n - 2 * zMonomialF ℚ 3 n := by
    rw [zMonomialF_two_eq, zMonomialF_three_eq]
    field_simp
    ring
  have key : (zPrimitive fun l ↦ (n - 1 : ℚ) * l) - (zPrimitive fun l ↦ 2 * zMonomialF ℚ 2 l)
              = zPrimitive ((fun (l : ℤ) ↦ (l : ℚ) * (n - l))) := by
    rw [← zPrimitive_sub]
    apply congr_arg zPrimitive
    ext l
    simp [zMonomialF_two_eq]
    ring
  simp_rw [obs, ← key, zPrimitive_mul_left]
  dsimp
  congr
  ext m
  rw [zMonomialF_one_eq]

lemma bosonic_sugawara_cc_calc_nat (n : ℕ) :
    ∑ l ∈ Finset.range n, (l : ℚ) * (n - l) = (n^3 - n) / 6 := by
  have key := bosonic_sugawara_cc_calc n
  simp only [Int.cast_natCast, Nat.cast_nonneg, zPrimitive_apply_of_nonneg, Int.toNat_natCast]
    at key
  rw [← key]

end central_charge_calculation

end Sugawara_boson -- section

end VirasoroProject -- namespace
