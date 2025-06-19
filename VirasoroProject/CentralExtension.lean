/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import VirasoroProject.LieCohomologySmallDegree

/-!
# Central extensions of Lie algebras defined by 2-cocycles

This file defines the central extension of a Lie algebra determined by a 2-cocycle. It is proven
that two central extensions are isomorphic if the corresponding cocycles differ by a coboundary.

## Main definitions

* `LieTwoCocycle.CentralExtension`: The central extension of a Lie algebra 𝓖 by an abelian Lie
  algebra 𝓐 defined by a 2-cocycle γ ∈ H²(𝓖,𝓐).
* `LieTwoCocycle.CentralExtension.equiv_of_lieTwoCoboundary`: An isomorphism between the central
  extensions defined by two 2-cocycles which differ by a coboundary.

## Main statements

* `LieTwoCocycle.CentralExtension.instLieAlgebra`: The central extension defined by a 2-cocycle
  is a Lie algebra.

## Implementation notes

`LieTwoCocycle.CentralExtension` is the concrete construction of a central extension. The defining
property (characteristic predicate) of central extensions is `IsCentralExtension`
(see the file `IsCentralExtension.lean`.)

## Tags

Lie algebra, central extension, 2-cocycle

-/

namespace VirasoroProject

universe u
variable (𝕜 : Type*) [CommRing 𝕜]
variable (𝓖 𝓐 : Type u) [LieRing 𝓖] [AddCommGroup 𝓐] [LieAlgebra 𝕜 𝓖] [Module 𝕜 𝓐]

variable {𝕜 𝓖 𝓐}

section LieTwoCocycle.CentralExtension

/-! ### Lie algebra central extensions determined by 2-cocycles -/

namespace LieTwoCocycle

set_option linter.unusedVariables false in
/-- The underlying type of the central extension of Lie algebras determined by a Lie
algebra 2-cocycle. -/
def CentralExtension (γ : LieTwoCocycle 𝕜 𝓖 𝓐) := 𝓖 × 𝓐

variable {γ : LieTwoCocycle 𝕜 𝓖 𝓐}

namespace CentralExtension

@[ext] lemma ext {Z W : γ.CentralExtension} (hX : Z.1 = W.1) (hA : Z.2 = W.2) :
    Z = W := Prod.ext hX hA

/-- Coercion of an element in a central extension to a pair. -/
def coeProd (Z : γ.CentralExtension) : 𝓖 × 𝓐 := Z

instance : AddCommGroup (γ.CentralExtension) := Prod.instAddCommGroup

instance : Module 𝕜 (γ.CentralExtension) := Prod.instModule

lemma add_def (Z₁ Z₂ : γ.CentralExtension) :
  Z₁ + Z₂ = ⟨Z₁.1 + Z₂.1, Z₁.2 + Z₂.2⟩ := rfl

lemma smul_def (c : 𝕜) (Z : γ.CentralExtension) :
  c • Z = ⟨c • Z.1, c • Z.2⟩ := rfl

@[simp] lemma add_fst (Z W : γ.CentralExtension) :
    (Z + W).1 = Z.1 + W.1 := rfl

@[simp] lemma add_snd (Z W : γ.CentralExtension) :
    (Z + W).2 = Z.2 + W.2 := rfl

@[simp] lemma smul_fst (c : 𝕜) (Z : γ.CentralExtension) :
    (c • Z).1 = c • Z.1 := rfl

@[simp] lemma smul_snd (c : 𝕜) (Z : γ.CentralExtension) :
    (c • Z).2 = c • Z.2 := rfl

end CentralExtension -- namespace

variable (γ)

open LinearMapClass RingHom in
/-- The Lie bracket in a central extension defined by a Lie algebra 2-cocycle. -/
def bracket : γ.CentralExtension
      →ₗ[𝕜] γ.CentralExtension →ₗ[𝕜] γ.CentralExtension where
  toFun := fun ⟨X,_⟩ ↦ {
    toFun := fun ⟨Y,_⟩ ↦ ⟨⁅X,Y⁆, γ X Y⟩
    map_add' := by intros ; simp_all only [lie_add, map_add] ; rfl
    map_smul' := by intros ; simp_all only [lie_smul, map_smul, id_apply] ; rfl }
  map_add' := by
    intros
    simp_all only [add_lie, map_add, LinearMap.add_apply]
    rfl
  map_smul' := by
    intros
    simp_all only [smul_lie, map_smul, LinearMap.smul_apply, id_apply]
    rfl

@[simp] lemma bracket_apply (Z W : γ.CentralExtension) :
    γ.bracket Z W = ⟨⁅Z.fst, W.fst⁆, γ Z.fst W.fst⟩ := rfl

lemma bracket_self (Z : γ.CentralExtension) :
    γ.bracket Z Z = 0 := by
  simp
  rfl

lemma bracket_smul (c : 𝕜) (Z W : γ.CentralExtension) :
    γ.bracket Z (c • W) = c • γ.bracket Z W := by
  simp only [LinearMapClass.map_smul, LieTwoCocycle.bracket_apply]

lemma bracket_leibniz (Z W₁ W₂ : γ.CentralExtension) :
    γ.bracket Z (γ.bracket W₁ W₂)
      = γ.bracket (γ.bracket Z W₁) W₂
        + γ.bracket W₁ (γ.bracket Z W₂) := by
  simp only [γ.bracket_apply]
  ext
  · exact leibniz_lie Z.1 W₁.1 W₂.1
  · apply γ.leibniz

namespace CentralExtension

/-- The central extension is a Lie ring. -/
instance : LieRing γ.CentralExtension where
  bracket Z W := γ.bracket Z W
  add_lie Z₁ Z₂ W := by simp
  lie_add Z W₁ W₂ := by simp ; rfl
  lie_self := γ.bracket_self
  leibniz_lie Z₁ Z₂ W := γ.bracket_leibniz Z₁ Z₂ W

/-- The central extension is a Lie algebra. -/
instance : LieAlgebra 𝕜 γ.CentralExtension where
  lie_smul := γ.bracket_smul

lemma lie_def (Z W : γ.CentralExtension) :
    ⁅Z, W⁆ = ⟨⁅Z.1, W.1⁆, γ Z.1 W.1⟩ := rfl

@[simp] lemma lie_fst (Z W : γ.CentralExtension) :
    ⁅Z, W⁆.1 = ⁅Z.1, W.1⁆ := rfl

@[simp] lemma lie_snd (Z W : γ.CentralExtension) :
    ⁅Z, W⁆.2 = γ Z.1 W.1 := rfl

end CentralExtension -- namespace

end LieTwoCocycle -- namespace

variable (β : LieOneCocycle 𝕜 𝓖 𝓐)
variable (γ)

/-- A Lie algebra homomorphism between two central extensions determined by cocycles
which differ by a coboundary. -/
def LieOneCocycle.bdryHom :
    (γ.CentralExtension) →ₗ⁅𝕜⁆ (γ + β.bdry).CentralExtension where
  toFun := fun Z ↦ ⟨Z.1, Z.2 + β Z.1⟩
  map_add' Z W := by
    ext
    · rfl
    · calc Z.2 + W.2 + β (Z.1 + W.1)
       _ = Z.2 + β Z.1 + (W.2 + β W.1)                   := by simp only [map_add] ; ac_rfl
       _ = ((Z.1, Z.2 + β Z.1) + (W.1, W.2 + β W.1)).2   := by rfl
  map_smul' c Z := by
    ext
    · rfl
    · calc ((c • Z).1, (c • Z).2 + β (c • Z).1).2
       _ = c • Z.2 + β (c • Z.1)           := by rfl
       _ = c • (Z.2 + β Z.1)               := by simp only [LinearMapClass.map_smul, smul_add]
       _ = (c • (Z.1, Z.2 + β Z.1)).2      := by rfl
  map_lie' := by
    intro Z W
    ext <;> rfl

namespace LieTwoCocycle.CentralExtension

/-- Annoyingly the dependent types make it difficult to identify central extensions with equal
but not definitionally equal cocycles (e.g. `γ + (β₁ + β₂).bdry` vs. `(γ + β₁.bdry) + β₂.bdry`).
This isomorphism allows to  -/
def congr {γ₁ γ₂ : LieTwoCocycle 𝕜 𝓖 𝓐} (h : γ₁ = γ₂) :
    γ₁.CentralExtension ≃ₗ⁅𝕜⁆ γ₂.CentralExtension where
  toFun := fun Z ↦ ⟨Z.1, Z.2⟩
  map_add' Z₁ Z₂ := rfl
  map_smul' c Z := rfl
  map_lie' := by
    intro Z₁ Z₂
    ext <;>
    · simp only [lie_def, h, Prod.mk.eta] ; rfl
  invFun := fun Z ↦ ⟨Z.1, Z.2⟩
  left_inv := by
    intro Z
    ext <;> dsimp only
  right_inv := by
    intro Z
    ext <;> dsimp only

lemma congr_apply {γ₁ γ₂ : LieTwoCocycle 𝕜 𝓖 𝓐} (h : γ₁ = γ₂) (Z : γ₁.CentralExtension) :
    congr h Z = ⟨Z.1, Z.2⟩ := rfl

@[simp] lemma congr_trans {γ₁ γ₂ γ₃ : LieTwoCocycle 𝕜 𝓖 𝓐} (h₁₂ : γ₁ = γ₂) (h₂₃ : γ₂ = γ₃) :
    (congr h₁₂).trans (congr h₂₃) = (congr (h₁₂.trans h₂₃)) :=
  rfl

lemma congr_congr_symm {γ₁ γ₂ : LieTwoCocycle 𝕜 𝓖 𝓐} (h : γ₁ = γ₂) :
    (congr h).trans (congr h.symm) = LieEquiv.refl :=
  rfl

lemma hom_of_coboundary_refl (γ : LieTwoCocycle 𝕜 𝓖 𝓐) :
    congr (Eq.refl γ) = LieEquiv.refl (R := 𝕜) (L₁ := γ.CentralExtension) :=
  rfl

lemma hom_of_coboundary_add (γ₁ γ₂ γ₃ : LieTwoCocycle 𝕜 𝓖 𝓐)
    (β₁ β₂ : LieOneCocycle 𝕜 𝓖 𝓐) (h₂ : γ₁ + β₁.bdry = γ₂) (h₃ : γ₂ + β₂.bdry = γ₃) :
    ((congr h₃).toLieHom.comp (β₂.bdryHom γ₂)).comp ((congr h₂).toLieHom.comp (β₁.bdryHom γ₁))
      = (congr (show γ₁ + (β₁ + β₂).bdry = γ₃ by rw [← h₃, ← h₂] ; ac_rfl)).toLieHom.comp
          ((β₁ + β₂).bdryHom γ₁) := by
  ext Z
  · rfl
  · simp only [LieTwoCocycle.CentralExtension.congr, Prod.mk.eta, LieOneCocycle.bdryHom,
               LieHom.comp_apply, LieHom.coe_mk]
    ac_rfl

/-- A Lie algebra isomorphism between two central extensions determined by cocycles
which differ by a coboundary. -/
noncomputable def equiv_of_lieTwoCoboundary {γ' : LieTwoCocycle 𝕜 𝓖 𝓐}
    (h : γ' - γ ∈ LieTwoCoboundary 𝕜 𝓖 𝓐) :
    (γ.CentralExtension) ≃ₗ⁅𝕜⁆ (γ'.CentralExtension) := by
  -- TODO: I should not construct data in tactic mode, but this is tedious to write in term mode...
  simp only [LinearMap.mem_range] at h
  set hβ := Exists.choose_spec h
  set β := Exists.choose h
  have obs : γ + β.bdry = γ' := by
    change γ + lieOneCocycle_bdryHom _ _ _ β = γ' ; simp [hβ]
  have obs' : γ' + -β.bdry = γ := by
    change γ' - lieOneCocycle_bdryHom _ _ _ β = γ ; simp [hβ]
  set f := (LieTwoCocycle.CentralExtension.congr obs).toLieHom.comp <| β.bdryHom γ
  set g := (LieTwoCocycle.CentralExtension.congr obs').toLieHom.comp <| (-β).bdryHom γ'
  apply LieEquiv.mk_of_comp_eq_id (f := f) (g := g)
  · convert LieTwoCocycle.CentralExtension.hom_of_coboundary_add γ γ' γ β (-β) obs obs'
    ext1 Z
    simp only [LieHom.coe_id, id_eq, LieTwoCocycle.CentralExtension.congr, Prod.mk.eta,
      LieOneCocycle.bdryHom, add_neg_cancel, LieHom.comp_apply, LieHom.coe_mk]
    ext
    · rfl
    · simp only [left_eq_add]
      rfl
  · convert LieTwoCocycle.CentralExtension.hom_of_coboundary_add γ' γ γ' (-β) β obs' obs
    ext1 Z
    simp only [LieHom.coe_id, id_eq, LieTwoCocycle.CentralExtension.congr, Prod.mk.eta,
      LieOneCocycle.bdryHom, add_neg_cancel, LieHom.comp_apply, LieHom.coe_mk]
    ext
    · rfl
    · simp only [neg_add_cancel, left_eq_add]
      rfl

end CentralExtension -- namespace

end LieTwoCocycle -- namespace

end LieTwoCocycle.CentralExtension -- section

end VirasoroProject -- namespace
