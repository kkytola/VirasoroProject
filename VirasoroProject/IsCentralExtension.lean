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
a Lie algebra. It is proven that central extension defined by a 2-cocycle satisfy this characteristic
predicate.

## Main definitions

* `LieAlgebra.IsCentralExtension`: The abstract definition (characteristic predicate) of a
  central extension of a Lie algebra 𝓖 by an abelian Lie algebra 𝓐: there exists a short exact
  sequence 0 ⟶ 𝓐 ⟶ 𝓔 ⟶ 𝓖 ⟶ 0 of Lie algebras, where the image of 𝓐 is contained in the centre
  of 𝓔.
* `LieTwoCocycle.CentralExtension.emb`: Given a 2-cocycle γ ∈ C²(𝓖,𝓐) and the correspondingly
  constructed central extension 𝓔, this is the map 𝓐 ⟶ 𝓔 in the short exact sequence.
* `LieTwoCocycle.CentralExtension.proj`: Given a 2-cocycle γ ∈ C²(𝓖,𝓐) and the correspondingly
  constructed central extension 𝓔, this is the map 𝓔 ⟶ 𝓖 in the short exact sequence.

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
variable {𝓖 𝓐 : Type u} [LieRing 𝓖] [LieAlgebra 𝕜 𝓖] [LieRing 𝓐] [LieAlgebra 𝕜 𝓐]

/-- An extension `𝓔` of a Lie algebra `𝓖` by a Lie algebra `𝓐` is a short exact sequence
`0 ⟶ 𝓐 ⟶ 𝓔 ⟶ 𝓖 ⟶ 0`. The class `LieAlgebra.IsExtension` bundles the maps `𝓐 ⟶ 𝓔` and
`𝓔 ⟶ 𝓖` together with their trivial kernel and full range, respectively, and the exactness
in the middle. -/
class LieAlgebra.IsExtension (𝓔 : Type u) [LieRing 𝓔] [LieAlgebra 𝕜 𝓔]
    (i : 𝓐 →ₗ⁅𝕜⁆ 𝓔) (p : 𝓔 →ₗ⁅𝕜⁆ 𝓖) : Prop where
  ker_eq_bot : i.ker = ⊥
  range_eq_top : p.range = ⊤
  exact : i.range = p.ker

/-- A central extension `𝓔` of a Lie algebra `𝓖` by a Lie algebra `𝓐` is an extension
`0 ⟶ 𝓐 ⟶ 𝓔 ⟶ 𝓖 ⟶ 0` where the image of `𝓐` is contained in the centre of `𝓔`. -/
class LieAlgebra.IsCentralExtension {𝓔 : Type u} [LieRing 𝓔] [LieAlgebra 𝕜 𝓔]
    (i : 𝓐 →ₗ⁅𝕜⁆ 𝓔) (p : 𝓔 →ₗ⁅𝕜⁆ 𝓖) extends IsExtension 𝓔 i p where
  central : ∀ (A : 𝓐), ∀ (E : 𝓔), ⁅i A, E⁆ = 0

end IsCentralExtension

section LieTwoCocycle.CentralExtension

/-! ### Lie algebra central extensions defined by 2-cocycles -/

universe u
variable {𝕜 : Type u} [CommRing 𝕜]
variable {𝓖 𝓐 : Type u} [LieRing 𝓖] [LieAlgebra 𝕜 𝓖] [LieRing 𝓐] [LieAlgebra 𝕜 𝓐]

variable (γ : LieTwoCocycle 𝕜 𝓖 𝓐)

namespace LieTwoCocycle.CentralExtension

/-- If `𝓔` is the (central) extension of `𝓖` by `𝓐` defined by a 2-cocycle `γ ∈ C²(𝓖,𝓐)`,
then `LieTwoCocycle.CentralExtension.emb` gives the corresponding embedding `𝓐 ⟶ 𝓔`. -/
def emb [IsLieAbelian 𝓐] : 𝓐 →ₗ⁅𝕜⁆ γ.CentralExtension where
  toFun := fun A ↦ ⟨0, A⟩
  map_add' A₁ A₂ := by simp [add_def]
  map_smul' c A := by simp [smul_def]
  map_lie' := by intro A₁ A₂ ; simp [lie_def]

/-- If `𝓔` is the (central) extension of `𝓖` by `𝓐` defined by a 2-cocycle `γ ∈ C²(𝓖,𝓐)`,
then `LieTwoCocycle.CentralExtension.proj` gives the corresponding projection `𝓔 ⟶ 𝓖`. -/
def proj : γ.CentralExtension →ₗ⁅𝕜⁆ 𝓖 where
  toFun := fun ⟨X, _⟩ ↦ X
  map_add' := by intro ⟨X₁, A₁⟩ ⟨X₂, A₂⟩ ; rfl
  map_smul' := by intro c ⟨X, A⟩ ; rfl
  map_lie' := by intro ⟨X₁, A₁⟩ ⟨X₂, A₂⟩ ; rfl

lemma range_proj_eq_top :
    (LieTwoCocycle.CentralExtension.proj γ).range = ⊤ :=
  (LieHom.range_eq_top (proj γ)).mpr fun X ↦ ⟨⟨X, 0⟩, rfl⟩

lemma ker_emb_eq_bot [IsLieAbelian 𝓐] :
    (LieTwoCocycle.CentralExtension.emb γ).ker = ⊥ :=
  (LieHom.ker_eq_bot (emb γ)).mpr fun _ _ hA ↦ congr_arg (fun Z ↦ Z.2) hA

lemma mem_range_emb_iff [IsLieAbelian 𝓐] (Z : γ.CentralExtension) :
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
  refine ⟨?_, ?_⟩
  · intro h ; simpa [proj]
  · intro h ; simpa only [proj, LieHom.coe_mk] using h

lemma range_emb_eq_ker_proj [IsLieAbelian 𝓐] :
    (LieTwoCocycle.CentralExtension.emb γ).range = (LieTwoCocycle.CentralExtension.proj γ).ker := by
  ext Z
  change Z ∈ (LieTwoCocycle.CentralExtension.emb γ).range ↔ Z ∈ (LieTwoCocycle.CentralExtension.proj γ).ker
  rw [mem_range_emb_iff, mem_ker_proj_iff]

/-- If `𝓔` is the (central) extension of `𝓖` by `𝓐` defined by a 2-cocycle `γ ∈ C²(𝓖,𝓐)`,
then `𝓔` is an extension of `𝓖` by `𝓐` in the sense that there is a short exact sequence
`0 ⟶ 𝓐 ⟶ 𝓔 ⟶ 𝓖 ⟶ 0` where the two maps are `LieTwoCocycle.CentralExtension.emb` and
`LieTwoCocycle.CentralExtension.proj`. -/
instance isExtension [IsLieAbelian 𝓐] :
    LieAlgebra.IsExtension _ (emb γ) (proj γ) where
  ker_eq_bot := ker_emb_eq_bot γ
  range_eq_top := range_proj_eq_top γ
  exact := range_emb_eq_ker_proj γ

/-- If `𝓔` is the central extension of `𝓖` by `𝓐` defined by a 2-cocycle `γ ∈ C²(𝓖,𝓐)`,
then `𝓔` is a central extension of `𝓖` by `𝓐` in the sense that there is a short exact sequence
`0 ⟶ 𝓐 ⟶ 𝓔 ⟶ 𝓖 ⟶ 0` where the two maps are `LieTwoCocycle.CentralExtension.emb` and
`LieTwoCocycle.CentralExtension.proj` and the image of `𝓐` is contained in the centre of `𝓔`. -/
instance isCentralExtension [IsLieAbelian 𝓐] (γ : LieTwoCocycle 𝕜 𝓖 𝓐) :
    LieAlgebra.IsCentralExtension (emb γ) (proj γ) where
  __ := LieTwoCocycle.CentralExtension.isExtension γ
  central := by
    intro A Z
    simp only [emb, LieHom.coe_mk, lie_def, zero_lie, map_zero, LinearMap.zero_apply]
    rfl

noncomputable def stdSection [IsLieAbelian 𝓐] (γ : LieTwoCocycle 𝕜 𝓖 𝓐) :
    𝓖 →ₗ[𝕜] γ.CentralExtension where
  toFun X := ⟨X, 0⟩
  map_add' X₁ X₂ := by rw [LieTwoCocycle.CentralExtension.add_def] ; simp
  map_smul' c X := by rw [LieTwoCocycle.CentralExtension.smul_def] ; simp

lemma stdSection_prop [IsLieAbelian 𝓐] (γ : LieTwoCocycle 𝕜 𝓖 𝓐) :
    proj γ ∘ₗ stdSection γ = (1 : 𝓖 →ₗ[𝕜] 𝓖) :=
  rfl

end LieTwoCocycle.CentralExtension --namespace

end LieTwoCocycle.CentralExtension -- section


section Basis

namespace LieAlgebra.IsCentralExtension

universe u u'
variable {𝕜 : Type u} [CommRing 𝕜]
variable {𝓖 𝓐 𝓔 : Type u}
variable [LieRing 𝓖] [LieAlgebra 𝕜 𝓖] [LieRing 𝓐] [LieAlgebra 𝕜 𝓐] [LieRing 𝓔] [LieAlgebra 𝕜 𝓔]

/-- A basis of a central extension of Lie algebras constructed from a section and bases of the
extending Lie algebras. -/
noncomputable def basis
    {i : 𝓐 →ₗ⁅𝕜⁆ 𝓔} {p : 𝓔 →ₗ⁅𝕜⁆ 𝓖} (cext : LieAlgebra.IsCentralExtension i p)
    (σ : 𝓖 →ₗ[𝕜] 𝓔) (hσ : p.toLinearMap ∘ₗ σ = 1)
    {ιA ιG  : Type u'} (basA : Basis ιA 𝕜 𝓐) (basG : Basis ιG 𝕜 𝓖) :
    Basis (ιA ⊕ ιG) 𝕜 𝓔 := by
  apply @ses_basis 𝕜 _ 𝓐 𝓔 𝓖 _ _ _ _ _ _ i.toLinearMap p.toLinearMap σ ιA ιG basA basG
  · exact (LieSubmodule.mk_eq_bot_iff.mp cext.ker_eq_bot)
  · exact congr_arg LieSubalgebra.toSubmodule cext.exact
  · exact hσ

@[simp] lemma basis_eq_of_left
    {i : 𝓐 →ₗ⁅𝕜⁆ 𝓔} {p : 𝓔 →ₗ⁅𝕜⁆ 𝓖} (cext : LieAlgebra.IsCentralExtension i p)
    (σ : 𝓖 →ₗ[𝕜] 𝓔) (hσ : p.toLinearMap ∘ₗ σ = 1)
    {ιA ιG  : Type u'} (basA : Basis ιA 𝕜 𝓐) (basG : Basis ιG 𝕜 𝓖) (ia : ιA):
    basis cext σ hσ basA basG (Sum.inl ia) = i (basA ia) := by
  simp [basis]

@[simp] lemma basis_eq_of_right
    {i : 𝓐 →ₗ⁅𝕜⁆ 𝓔} {p : 𝓔 →ₗ⁅𝕜⁆ 𝓖} (cext : LieAlgebra.IsCentralExtension i p)
    (σ : 𝓖 →ₗ[𝕜] 𝓔) (hσ : p.toLinearMap ∘ₗ σ = 1)
    {ιA ιG  : Type u'} (basA : Basis ιA 𝕜 𝓐) (basG : Basis ιG 𝕜 𝓖) (ig : ιG):
    basis cext σ hσ basA basG (Sum.inr ig) = σ (basG ig) := by
  simp [basis]

end LieAlgebra.IsCentralExtension

end Basis

end VirasoroProject -- namespace
