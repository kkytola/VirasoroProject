/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Order.CompletePartialOrder

/-!
# Sections of short exact sequences

This file contains basics of sections of short exact sequences. In particular it is proved that
in a short exact sequence of

## Main definitions

* `MonoidHom.corrector`: Given a short exact sequence `1 ⟶ H ⟶ K ⟶ G ⟶ 1` of groups (with maps
  `ι : H → K` and `π : K → G`) and a section `σ : G → K` of it (`π ∘ σ = id_G`), the corrector
  `γ : K → H` is the unique function such that `k = σ(π(k)) * ι(γ(k))` for any `k : K`.
* `MonoidHom.correctorHom`: Given a short exact sequence `0 ⟶ U ⟶ V ⟶ W ⟶ 0` of abelian groups
  and a section `σ : W → V` of it, the corrector `γ : V → U` is a group homomorphism, uniquely
  specified by the condition `v = σ(π(v)) + ι(γ(v))` for any `v : V`.
* `LinearMap.choose_section`: Given a short exact sequence `0 ⟶ U ⟶ V ⟶ W ⟶ 0` of modules,
  where `W` is a free module, one can choose a linear section `σ : W → V` of the short exact
  sequence.
* `LinearMap.corrector`: Given a short exact sequence `0 ⟶ U ⟶ V ⟶ W ⟶ 0` of modules
  and a section `σ : W → V`, the corrector `γ : V → U` is a linear map, uniquely
  specified by the condition `v = σ(π(v)) + ι(γ(v))` for any `v : V`.
* `ses_basis`: Given a short exact sequence `0 ⟶ U ⟶ V ⟶ W ⟶ 0` of modules and a section
  `σ : W → V` of it, one can construct a basis of `V` from a basis of `W` and a basis of `U`.

## Main statements

* `ses_directSum_isInternal`: The property `v = σ(π(v)) + ι(γ(v))` of a corrector `γ` of a
  section `σ` of a short exact sequence `0 ⟶ U ⟶ V ⟶ W ⟶ 0` of modules gives an internal
  direct sum decomposition `V = σ(W) ⊕ ι(U)`.

## Tags

short exact sequence

-/

section group_section

namespace MonoidHom

variable {U V W : Type*} [Group U] [Group V] [Group W]
variable {f : U →* V} {g : V →* W}
variable {σ : W → V}

/-- Uniqueness of the "corrector" for a given vector. -/
@[to_additive] lemma unique_corrector (hf : f.ker = ⊥) (v : V) (u₁ u₂ : U)
    (h₁ : v = σ (g v) * f u₁) (h₂ : v = σ (g v) * f u₂) :
    u₁ = u₂ := by
  apply (ker_eq_bot_iff f).mp hf
  nth_rw 1 [h₁] at h₂
  simpa using h₂

/-- Existence of the "corrector" for a given vector. -/
@[to_additive] lemma exists_corrector (hfg : f.range = g.ker) (hgσ : g ∘ σ = _root_.id) (v : V) :
    ∃ (u : U), v = σ (g v) * f u := by
  suffices (σ (g v))⁻¹ * v ∈ g.ker by
    obtain ⟨u, hu⟩ : ∃ x, f x = (σ (g v))⁻¹ * v := by simpa [← hfg] using this
    refine ⟨u, by simp [hu]⟩
  have := congr_fun hgσ (g v)
  simp only [Function.comp_apply] at this
  simp [this]

/-- The corrector function `γ : V → U` associated to a section `σ : W → V` of a
short exact sequence `1 ⟶ U ⟶ V ⟶ W ⟶ 1`. -/
@[to_additive] noncomputable def corrector
    (hfg : f.range = g.ker) (hgσ : g ∘ σ = _root_.id) (v : V) :
    U :=
  (exists_corrector hfg hgσ v).choose

/-- The corrector map `γ : V → U` satisfies `v = σ(g(v)) * f(γ(v))` for any `v : V`. -/
@[to_additive] lemma corrector_spec (hfg : f.range = g.ker) (hgσ : g ∘ σ = _root_.id) (v : V) :
    v = σ (g v) * f (corrector hfg hgσ v) :=
  (exists_corrector hfg hgσ v).choose_spec

@[to_additive] lemma corrector_eq_iff
    (hf : f.ker = ⊥) (hfg : f.range = g.ker) (hgσ : g ∘ σ = _root_.id) (v : V) (u : U) :
    corrector hfg hgσ v = u ↔ v = σ (g v) * f u :=
  ⟨fun h ↦ h ▸ corrector_spec hfg hgσ v, unique_corrector hf v _ _ (corrector_spec hfg hgσ v)⟩

@[to_additive] lemma image_corrector_eq_self_of_mem_ker {σ : W →* V} (hfg : f.range = g.ker)
    (hgσ : g ∘ σ = _root_.id) {v : V} (hv : v ∈ g.ker) :
    f (corrector hfg hgσ v) = v := by
  rw [mem_ker] at hv
  nth_rw 2 [corrector_spec hfg hgσ v]
  simp [hv]

@[to_additive] lemma corrector_one {σ : W →* V}
    (hf : f.ker = ⊥) (hfg : f.range = g.ker) (hgσ : g ∘ σ = _root_.id) :
    corrector hfg hgσ 1 = 1 := by
  apply unique_corrector hf 1 _ _ (corrector_spec hfg hgσ 1)
  simp

end MonoidHom

end group_section


section comm_group_section

namespace MonoidHom

variable {U V W : Type*} [Group U] [CommGroup V] [Group W]
variable {f : U →* V} {g : V →* W}

@[to_additive] lemma corrector_mul {σ : W →* V}
    (hf : f.ker = ⊥) (hfg : f.range = g.ker) (hgσ : g ∘ σ = _root_.id) (v₁ v₂ : V) :
    corrector hfg hgσ (v₁ * v₂) = corrector hfg hgσ v₁ * corrector hfg hgσ v₂ := by
  apply unique_corrector hf (v₁ * v₂) _ _ (corrector_spec hfg hgσ (v₁ * v₂))
  nth_rw 1 [corrector_spec hfg hgσ v₁]
  nth_rw 1 [corrector_spec hfg hgσ v₂]
  simp only [map_mul, mul_assoc, mul_right_inj]
  simpa [← mul_assoc, mul_left_inj] using CommGroup.mul_comm _ _

/-- The corrector homomorphism `γ : V → U` associated to a multiplicative section `σ : W → V` of a
short exact sequence `1 ⟶ U ⟶ V ⟶ W ⟶ 1`. -/
@[to_additive] noncomputable def correctorHom {σ : W →* V}
    (hf : f.ker = ⊥) (hfg : f.range = g.ker) (hgσ : g.comp σ = MonoidHom.id _) :
    V →* U where
  toFun := @corrector U V W _ _ _ f g σ.toFun hfg
    (by ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w)
  map_one' := corrector_one hf hfg ..
  map_mul' := corrector_mul hf hfg (by ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w)

@[to_additive] lemma correctorHom_eq_iff {σ : W →* V}
    (hf : f.ker = ⊥) (hfg : f.range = g.ker) (hgσ : g.comp σ = MonoidHom.id _)
    (v : V) (u : U) :
    correctorHom hf hfg hgσ v = u ↔ v = σ (g v) * f u := by
  refine corrector_eq_iff hf hfg ?_ v u
  ext w
  exact congrFun (congrArg DFunLike.coe hgσ) w

@[to_additive] lemma image_correctorHom_eq_self_of_mem_ker {σ : W →* V} (hf : f.ker = ⊥)
    (hfg : f.range = g.ker) (hgσ : g.comp σ = MonoidHom.id _) {v : V} (hv : v ∈ g.ker) :
    f (correctorHom hf hfg hgσ v) = v := by
  apply image_corrector_eq_self_of_mem_ker hfg ?_ hv
  ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w

end MonoidHom

end comm_group_section


section module_section

namespace LinearMap

open Module.Free in
/-- A choice of a linear section of a surjective linear map to a free module. -/
noncomputable def choose_section {𝕜 : Type*} [CommSemiring 𝕜] {V W : Type*}
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W] [Module.Free 𝕜 W]
    {g : V →ₗ[𝕜] W} (hg : range g = ⊤) :
    W →ₗ[𝕜] V :=
  have aux (i : ChooseBasisIndex 𝕜 W) : ∃ v, g v = (chooseBasis 𝕜 W) i :=
    range_eq_top.mp hg (chooseBasis 𝕜 W i)
  (chooseBasis 𝕜 W).constr 𝕜 fun i ↦ (aux i).choose

open Module.Free in
lemma choose_section_prop {𝕜 : Type*} [CommSemiring 𝕜] {V W : Type*}
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W] [Module.Free 𝕜 W]
    {g : V →ₗ[𝕜] W} (hg : range g = ⊤) :
    g ∘ₗ (choose_section hg) = 1 := by
  apply (chooseBasis 𝕜 W).ext fun i ↦ ?_
  have aux (i : ChooseBasisIndex 𝕜 W) : ∃ v, g v = (chooseBasis 𝕜 W) i :=
    range_eq_top.mp hg (chooseBasis 𝕜 W i)
  simp [choose_section, (aux i).choose_spec]

lemma choose_section_prop_apply {𝕜 : Type*} [CommSemiring 𝕜] {V W : Type*}
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W] [Module.Free 𝕜 W]
    {g : V →ₗ[𝕜] W} (hg : range g = ⊤) (w : W) :
    g (choose_section hg w) = w :=
  LinearMap.congr_fun (choose_section_prop hg) w

variable {𝕜 : Type*} [Ring 𝕜]
variable {U V W : Type*}
variable [AddCommGroup U] [Module 𝕜 U] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
variable {f : U →ₗ[𝕜] V} {g : V →ₗ[𝕜] W}

variable {σ : W →ₗ[𝕜] V}

open AddMonoidHom in
lemma correctorHom_smul (hf : f.toAddMonoidHom.ker = ⊥)
    (hfg : f.toAddMonoidHom.range = g.toAddMonoidHom.ker)
    (hgσ : g.toAddMonoidHom.comp σ.toAddMonoidHom = AddMonoidHom.id _) (c : 𝕜) (v : V) :
    correctorHom hf hfg hgσ (c • v) = c • correctorHom hf hfg hgσ v := by
  simp only [correctorHom, ZeroHom.toFun_eq_coe, toZeroHom_coe, toAddMonoidHom_coe]
  have aux : ↑g ∘ σ = _root_.id := by ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w
  apply unique_corrector hf (c • v) _ _ (corrector_spec hfg aux (c • v))
  nth_rw 1 [corrector_spec hfg aux v]
  simp

/-- The corrector linear map `γ : V → U` associated to a linear section `σ : W → V` of a
short exact sequence `0 ⟶ U ⟶ V ⟶ W ⟶ 0`. -/
noncomputable def corrector (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) :
    V →ₗ[𝕜] U where
  toFun := @AddMonoidHom.correctorHom U V W _ _ _ f g σ
      (congr_arg Submodule.toAddSubgroup hf)
      (congr_arg Submodule.toAddSubgroup hfg)
      (by ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w)
  map_add' := AddMonoidHom.map_add (AddMonoidHom.correctorHom _ _ _)
  map_smul' := by apply correctorHom_smul

/-- The corrector map `γ : V → U` satisfies `v = σ(g(v)) + f(γ(v))` for any `v : V`. -/
lemma corrector_spec (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) (v : V) :
    v = σ (g v) + f (corrector hf hfg hgσ v) :=
  @AddMonoidHom.corrector_spec U V W _ _ _ f g σ (congr_arg Submodule.toAddSubgroup hfg)
    (by ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w) v

lemma corrector_eq_iff (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) (v : V) (u : U) :
    corrector hf hfg hgσ v = u ↔ v = σ (g v) + f u := by
  apply AddMonoidHom.corrector_eq_iff
  · exact congr_arg Submodule.toAddSubgroup hf
  · exact congr_arg Submodule.toAddSubgroup hfg
  · ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w

lemma image_corrector_eq_self_of_mem_ker {σ : W →ₗ[𝕜] V} (hf : ker f = ⊥)
    (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) {v : V} (hv : v ∈ ker g) :
    f (corrector hf hfg hgσ v) = v :=
  @AddMonoidHom.image_correctorHom_eq_self_of_mem_ker U V W _ _ _ f g σ
    (congr_arg Submodule.toAddSubgroup hf) (congr_arg Submodule.toAddSubgroup hfg)
    (by ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w) v hv

end LinearMap


section basis

open LinearMap Module

variable {𝕜 : Type*} [Ring 𝕜]
variable {U V W : Type*}
variable [AddCommGroup U] [Module 𝕜 U] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
variable {f : U →ₗ[𝕜] V} {g : V →ₗ[𝕜] W} {σ : W →ₗ[𝕜] V}

universe u
variable {ιU : Type u} {ιW : Type u} (basU : Basis ιU 𝕜 U) (basW : Basis ιW 𝕜 W)

/-- A short exact sequence of modules together with a section gives an internal direct sum
decomposition. -/
lemma ses_directSum_isInternal (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) :
    DirectSum.IsInternal (fun (j : Bool) ↦ if j then range f else range σ) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · have aux (M : Submodule 𝕜 V) (M_le₁ : M ≤ range f) (M_le₀ : M ≤ range σ)
        {v : V} (v_in_M : v ∈ M) :
        v = 0 := by
      have obs₁ : σ (g v) = 0 := by
        obtain ⟨u, hu⟩ := M_le₁ v_in_M
        simp [← hu, mem_ker.mp <| hfg ▸ mem_range_self f u]
      have obs₀ : f ((corrector hf hfg hgσ) v) = 0 := by
        obtain ⟨w, hw⟩ := M_le₀ v_in_M
        have gv_eq_w : g v = w := by simpa [← hw] using LinearMap.congr_fun hgσ w
        have v_eq_σgv : v = σ (g v) := by nth_rw 1 [← hw] ; rw [← gv_eq_w]
        calc  f ((corrector hf hfg hgσ) v)
            = f 0         := by rw [(corrector_eq_iff hf hfg hgσ v 0).mpr (by simp [← v_eq_σgv])]
          _ = 0           := map_zero f
      rw [corrector_spec hf hfg hgσ v]
      simp [obs₁, obs₀]
    intro j M M_le M_le' v v_in_M
    simp only [Submodule.mem_bot]
    by_cases hj : j = true
    · simp only [hj, ↓reduceIte, ne_eq, Bool.not_eq_true, iSup_iSup_eq_left,
                 Bool.false_eq_true] at M_le M_le'
      exact aux M M_le M_le' v_in_M
    · simp only [hj, Bool.false_eq_true, ↓reduceIte, ne_eq, Bool.not_eq_false,
                 iSup_iSup_eq_left] at M_le M_le'
      exact aux M M_le' M_le v_in_M
  · rw [← top_le_iff]
    intro v _
    have key : v = ∑ (j : Bool), if j then f ((corrector hf hfg hgσ) v) else σ (g v) := by
      nth_rw 1 [corrector_spec hf hfg hgσ v, add_comm] ; simp
    rw [key]
    apply Submodule.sum_mem_iSup fun j ↦ by by_cases hj : j = true <;> simp [hj]

/-- From a short exact sequence of modules, a section of it, we can construct a basis of
the middle module from bases of the two other modules.
(See `ses_basis` for a more conveniently indexed basis.)-/
noncomputable def ses_basis' (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) :
    Basis ((j' : Bool) × (fun j ↦ if j then ιU else ιW) j') 𝕜 V := by
  apply (ses_directSum_isInternal hf hfg hgσ).collectedBasis
  let f_iso : U ≃ₗ[𝕜] range f :=
    LinearEquiv.ofBijective (f := f.rangeRestrict)
      ⟨(injective_rangeRestrict_iff f).mpr (ker_eq_bot.mp hf),
       surjective_rangeRestrict f⟩
  let σ_iso : W ≃ₗ[𝕜] range σ :=
    LinearEquiv.ofBijective (f := σ.rangeRestrict)
      ⟨(injective_rangeRestrict_iff σ).mpr <| injective_of_comp_eq_id σ g hgσ,
       surjective_rangeRestrict σ⟩
  intro j
  by_cases hj : j = true
  · erw [hj]
    exact basU.map f_iso
  · simp only [Bool.not_eq_true] at hj
    erw [hj]
    exact basW.map σ_iso

/-- From a short exact sequence of modules, a section of it, we can construct a basis of
the middle module from bases of the two other modules. -/
noncomputable def ses_basis (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) :
    Basis (ιU ⊕ ιW) 𝕜 V := by
  let auxBasis := ses_basis' basU basW hf hfg hgσ
  let β : ιU ⊕ ιW ≃ ((j' : Bool) × (fun j ↦ if j then ιU else ιW) j') := {
    toFun i := match i with
      | Sum.inl iu => ⟨true, iu⟩
      | Sum.inr ir => ⟨false, ir⟩
    invFun j := if hj : j.1 then (Sum.inl (by
        cases' j with jfst jsnd
        simpa [show jfst = true from hj] using jsnd))
      else (Sum.inr (by
        cases' j with jfst jsnd
        simpa [show jfst = false by simpa using hj] using jsnd))
    left_inv i := match i with
      | Sum.inl iu => rfl
      | Sum.inr ir => rfl
    right_inv j := if hj : j.1 then (by aesop) else (by aesop)
  }
  exact auxBasis.reindex (_root_.id β.symm)

@[simp] lemma ses_basis_eq_of_left (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1)
    (iu : ιU) :
    ses_basis basU basW hf hfg hgσ (Sum.inl iu) = f (basU iu) := by
  simp [ses_basis, ses_basis']

@[simp] lemma ses_basis_eq_of_right (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1)
    (iw : ιW) :
    ses_basis basU basW hf hfg hgσ (Sum.inr iw) = σ (basW iw) := by
  simp [ses_basis, ses_basis']

end basis

open AddHom

end module_section
