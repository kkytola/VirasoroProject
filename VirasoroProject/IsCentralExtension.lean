/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import VirasoroProject.CentralExtension
import VirasoroProject.SectionSES

/-!
# Abstract central extensions of Lie algebras (characteristic predicate)

This file defines the short exact sequence characteristic predicate for a central extension of
a Lie algebra. It is proven that central extension defined by a 2-cocycle satisfy this
characteristic predicate.

## Main definitions

* `LieAlgebra.IsCentralExtension`: The abstract definition (characteristic predicate) of a
  central extension of a Lie algebra 𝓰 by an abelian Lie algebra 𝓪: there exists a short exact
  sequence 0 ⟶ 𝓪 ⟶ 𝓮 ⟶ 𝓰 ⟶ 0 of Lie algebras, where the image of 𝓪 is contained in the centre
  of 𝓮.
* `LieTwoCocycle.CentralExtension.emb`: Given a 2-cocycle γ ∈ Z²(𝓰,𝓪) and the correspondingly
  constructed central extension 𝓮, this is the map 𝓪 ⟶ 𝓮 in the short exact sequence.
* `LieTwoCocycle.CentralExtension.proj`: Given a 2-cocycle γ ∈ Z²(𝓰,𝓪) and the correspondingly
  constructed central extension 𝓮, this is the map 𝓮 ⟶ 𝓰 in the short exact sequence.

## Main statements

* `LieTwoCocycle.CentralExtension.isCentralExtension`: The central extension defined by a 2-cocycle
  is a central extension in the abstract sense (it satisfies the characteristic predicate).

## Tags

Lie algebra, central extension, short exact sequence

-/

namespace VirasoroProject

section IsCentralExtension

/-! ### Lie algebra central extensions defined by short exact sequences -/

universe u
variable {𝕜 : Type u} [CommRing 𝕜]
variable {𝓰 𝓪 𝓮 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰] [LieRing 𝓪] [LieAlgebra 𝕜 𝓪]
         [LieRing 𝓮] [LieAlgebra 𝕜 𝓮]

/-- An extension `𝓮` of a Lie algebra `𝓰` by a Lie algebra `𝓪` is a short exact sequence
`0 ⟶ 𝓪 ⟶ 𝓮 ⟶ 𝓰 ⟶ 0`. The structure `LieAlgebra.IsExtension` bundles the maps `𝓪 ⟶ 𝓮` and
`𝓮 ⟶ 𝓰` together with their trivial kernel and full range, respectively, and the exactness
in the middle. -/
structure LieAlgebra.IsExtension (i : 𝓪 →ₗ⁅𝕜⁆ 𝓮) (p : 𝓮 →ₗ⁅𝕜⁆ 𝓰) : Prop where
  ker_eq_bot : i.ker = ⊥
  range_eq_top : p.range = ⊤
  exact : i.range = p.ker

/-- A central extension `𝓮` of a Lie algebra `𝓰` by a Lie algebra `𝓪` is an extension
`0 ⟶ 𝓪 ⟶ 𝓮 ⟶ 𝓰 ⟶ 0` where the image of `𝓪` is contained in the centre of `𝓮`. -/
structure LieAlgebra.IsCentralExtension {𝓮 : Type u} [LieRing 𝓮] [LieAlgebra 𝕜 𝓮]
    (i : 𝓪 →ₗ⁅𝕜⁆ 𝓮) (p : 𝓮 →ₗ⁅𝕜⁆ 𝓰) extends IsExtension i p where
  central : ∀ (A : 𝓪), ∀ (E : 𝓮), ⁅i A, E⁆ = 0

end IsCentralExtension

section LieTwoCocycle.CentralExtension

/-! ### Lie algebra central extensions defined by 2-cocycles -/

universe u
variable {𝕜 : Type u} [CommRing 𝕜]
variable {𝓰 𝓪 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰] [LieRing 𝓪] [LieAlgebra 𝕜 𝓪]

variable (γ : LieTwoCocycle 𝕜 𝓰 𝓪)

namespace LieTwoCocycle.CentralExtension

/-- If `𝓮` is the (central) extension of `𝓰` by `𝓪` defined by a 2-cocycle `γ ∈ Z²(𝓰,𝓪)`,
then `LieTwoCocycle.CentralExtension.emb` gives the corresponding embedding `𝓪 ⟶ 𝓮`. -/
def emb [IsLieAbelian 𝓪] : 𝓪 →ₗ⁅𝕜⁆ γ.CentralExtension where
  toFun := fun A ↦ ⟨0, A⟩
  map_add' A₁ A₂ := by simp [add_def]
  map_smul' c A := by simp [smul_def]
  map_lie' := by
    intro A₁ A₂
    simp only [lie_def, lie_zero, map_zero]
    exact Prod.ext rfl (trivial_lie_zero 𝓪 𝓪 A₁ A₂)

/-- If `𝓮` is the (central) extension of `𝓰` by `𝓪` defined by a 2-cocycle `γ ∈ Z²(𝓰,𝓪)`,
then `LieTwoCocycle.CentralExtension.proj` gives the corresponding projection `𝓮 ⟶ 𝓰`. -/
def proj : γ.CentralExtension →ₗ⁅𝕜⁆ 𝓰 where
  toFun := fun ⟨X, _⟩ ↦ X
  map_add' := by intro ⟨X₁, A₁⟩ ⟨X₂, A₂⟩ ; rfl
  map_smul' := by intro c ⟨X, A⟩ ; rfl
  map_lie' := by intro ⟨X₁, A₁⟩ ⟨X₂, A₂⟩ ; rfl

lemma range_proj_eq_top :
    (LieTwoCocycle.CentralExtension.proj γ).range = ⊤ :=
  (LieHom.range_eq_top (proj γ)).mpr fun X ↦ ⟨⟨X, 0⟩, rfl⟩

lemma ker_emb_eq_bot [IsLieAbelian 𝓪] :
    (LieTwoCocycle.CentralExtension.emb γ).ker = ⊥ :=
  (LieHom.ker_eq_bot (emb γ)).mpr fun _ _ hA ↦ congr_arg (fun Z ↦ Z.2) hA

lemma mem_range_emb_iff [IsLieAbelian 𝓪] (Z : γ.CentralExtension) :
    Z ∈ (LieTwoCocycle.CentralExtension.emb γ).range ↔ Z.1 = 0 := by
  rw [LieHom.mem_range]
  refine ⟨?_, ?_⟩
  · intro ⟨A, hA⟩
    simp [← hA, emb]
  · intro h
    use Z.2
    simp only [emb, LieHom.coe_mk]
    ext <;> simp_all

lemma mem_ker_proj_iff (Z : γ.CentralExtension) :
    Z ∈ (LieTwoCocycle.CentralExtension.proj γ).ker ↔ Z.1 = 0 := by
  rw [LieHom.mem_ker]
  obtain ⟨X, A⟩ := Z
  simp [proj]

lemma range_emb_eq_ker_proj [IsLieAbelian 𝓪] :
    (LieTwoCocycle.CentralExtension.emb γ).range = (LieTwoCocycle.CentralExtension.proj γ).ker := by
  ext Z
  change Z ∈ (LieTwoCocycle.CentralExtension.emb γ).range
        ↔ Z ∈ (LieTwoCocycle.CentralExtension.proj γ).ker
  rw [mem_range_emb_iff, mem_ker_proj_iff]

/-- If `𝓮` is the (central) extension of `𝓰` by `𝓪` defined by a 2-cocycle `γ ∈ Z²(𝓰,𝓪)`,
then `𝓮` is an extension of `𝓰` by `𝓪` in the sense that there is a short exact sequence
`0 ⟶ 𝓪 ⟶ 𝓮 ⟶ 𝓰 ⟶ 0` where the two maps are `LieTwoCocycle.CentralExtension.emb` and
`LieTwoCocycle.CentralExtension.proj`. -/
theorem isExtension [IsLieAbelian 𝓪] :
    LieAlgebra.IsExtension (emb γ) (proj γ) where
  ker_eq_bot := ker_emb_eq_bot γ
  range_eq_top := range_proj_eq_top γ
  exact := range_emb_eq_ker_proj γ

/-- If `𝓮` is the central extension of `𝓰` by `𝓪` defined by a 2-cocycle `γ ∈ Z²(𝓰,𝓪)`,
then `𝓮` is a central extension of `𝓰` by `𝓪` in the sense that there is a short exact sequence
`0 ⟶ 𝓪 ⟶ 𝓮 ⟶ 𝓰 ⟶ 0` where the two maps are `LieTwoCocycle.CentralExtension.emb` and
`LieTwoCocycle.CentralExtension.proj` and the image of `𝓪` is contained in the centre of `𝓮`. -/
theorem isCentralExtension [IsLieAbelian 𝓪] (γ : LieTwoCocycle 𝕜 𝓰 𝓪) :
    LieAlgebra.IsCentralExtension (emb γ) (proj γ) where
  __ := LieTwoCocycle.CentralExtension.isExtension γ
  central := by
    intro A Z
    simp only [emb, LieHom.coe_mk, lie_def, zero_lie, map_zero, LinearMap.zero_apply]
    rfl

/-- A standard section of a Lie algebra central extension associated to a Lie 2-cocycle. -/
noncomputable def stdSection (γ : LieTwoCocycle 𝕜 𝓰 𝓪) :
    𝓰 →ₗ[𝕜] γ.CentralExtension where
  toFun X := ⟨X, 0⟩
  map_add' X₁ X₂ := by rw [LieTwoCocycle.CentralExtension.add_def] ; simp
  map_smul' c X := by rw [LieTwoCocycle.CentralExtension.smul_def] ; simp

lemma stdSection_prop (γ : LieTwoCocycle 𝕜 𝓰 𝓪) :
    proj γ ∘ₗ stdSection γ = (1 : 𝓰 →ₗ[𝕜] 𝓰) :=
  rfl

end LieTwoCocycle.CentralExtension --namespace

end LieTwoCocycle.CentralExtension -- section


section Basis

namespace LieAlgebra.IsExtension

open Module

universe u u'
variable {𝕜 : Type u} [CommRing 𝕜]
variable {𝓰 𝓪 𝓮 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰] [LieRing 𝓪] [LieAlgebra 𝕜 𝓪]
         [LieRing 𝓮] [LieAlgebra 𝕜 𝓮]
variable {i : 𝓪 →ₗ⁅𝕜⁆ 𝓮} {p : 𝓮 →ₗ⁅𝕜⁆ 𝓰} (ex : LieAlgebra.IsExtension i p)
variable (σ : 𝓰 →ₗ[𝕜] 𝓮) (hσ : p.toLinearMap ∘ₗ σ = 1)

/-- A basis of a central extension of Lie algebras constructed from a section and bases of the
extending Lie algebras. -/
noncomputable def basis {ιA ιG  : Type u'} (basA : Basis ιA 𝕜 𝓪) (basG : Basis ιG 𝕜 𝓰) :
    Basis (ιA ⊕ ιG) 𝕜 𝓮 :=
  ses_basis basA basG (LieSubmodule.mk_eq_bot_iff.mp ex.ker_eq_bot)
    (congr_arg LieSubalgebra.toSubmodule ex.exact) hσ

@[simp] lemma basis_eq_of_left {ιA ιG  : Type u'} (basA : Basis ιA 𝕜 𝓪) (basG : Basis ιG 𝕜 𝓰)
    (ia : ιA) :
    basis ex σ hσ basA basG (Sum.inl ia) = i (basA ia) := by
  simp [basis]

@[simp] lemma basis_eq_of_right {ιA ιG  : Type u'} (basA : Basis ιA 𝕜 𝓪) (basG : Basis ιG 𝕜 𝓰)
    (ig : ιG):
    basis ex σ hσ basA basG (Sum.inr ig) = σ (basG ig) := by
  simp [basis]

end LieAlgebra.IsExtension

end Basis

end VirasoroProject -- namespace
