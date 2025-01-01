/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.Lie.Abelian
import VirasoroProject.ToMathlib.Algebra.Lie.Basic

/-!
# Lie algebra cohomology in degree two (for central extensions)

(*WARNING*: This file needs cleaning up. It was not the main goal and it was the first time I
tried to use multilinear maps in Lean.)

This file defines Lie algebra 2-cocycles and 2-coboundaries and constructs the Lie algebra
cohomology in degree two, with coefficients in a vector space (an Abelian Lie algebra).

## Main definitions

* `LieOneCocycle`: The set C¹(𝓖,𝓐) of 1-cocycles of a Lie algebra 𝓖 with coefficients in a
  vector space 𝓐.
* `LieTwoCocycle`: The set C²(𝓖,𝓐) of 2-cocycles of a Lie algebra 𝓖 with coefficients in a
  vector space 𝓐.
* `LieTwoCoboundary`: The subspace B²(𝓖,𝓐) ⊆ C²(𝓖,𝓐) of 2-coboundaries.
* `LieTwoCohomology`: The 2-cohomology H²(𝓖,𝓐) := C²(𝓖,𝓐) ⧸ B²(𝓖,𝓐) of a Lie algebra 𝓖 with
  coefficients in a vector space 𝓐.

## Main statements

* `LieTwoCocycle.toLieTwoCohomologyEquiv`: If 𝓖 is abelian, then the canonical projection
  from 2-cocycles to 2-cohomologies is a linear isomorphism.

## Implementation notes

This file needs some clean-up! (But it works for the purposes of concrete calculations of
central extensions etc.)

A reasonable thing to do would be to define Lie algebra cohomology in general degrees. But for
concrete applications, the special case of degree two probably deserves its own API. Once a
general definition is made, the API for the degree 2 case (especially central extensions)
could be refactored. (But even in the current generality, clean-up is needed here.)

## Tags

Lie algebra, cohomology

-/

namespace VirasoroProject

universe u
variable (𝕜 : Type*) [CommRing 𝕜]
variable (𝓖 𝓐 : Type u) [LieRing 𝓖] [AddCommGroup 𝓐] [LieAlgebra 𝕜 𝓖] [Module 𝕜 𝓐]

section LieOneCocycle

/-! ### Lie algebra 1-cocycles -/

/-- Lie algebra 1-cocycles. -/
@[ext] structure LieOneCocycle where
  /-- The underlying linear map of a Lie algebra 1-cocycle. -/
  toLinearMap : 𝓖 →ₗ[𝕜] 𝓐

instance : Zero (LieOneCocycle 𝕜 𝓖 𝓐) where
  zero := { toLinearMap := 0 }

instance : Add (LieOneCocycle 𝕜 𝓖 𝓐) where
  add β β' := { toLinearMap := β.toLinearMap + β'.toLinearMap }

instance : SMul 𝕜 (LieOneCocycle 𝕜 𝓖 𝓐) where
  smul c β := { toLinearMap := c • β.toLinearMap }

namespace LieOneCocycle

@[simp]
lemma toLinearMap_zero : (0 : LieOneCocycle 𝕜 𝓖 𝓐).toLinearMap = 0 := rfl

@[simp]
lemma toLinearMap_add (β β' : LieOneCocycle 𝕜 𝓖 𝓐) :
    (β + β').toLinearMap = β.toLinearMap + β'.toLinearMap := rfl

@[simp]
lemma toLinearMap_smul (c : 𝕜) (β : LieOneCocycle 𝕜 𝓖 𝓐) :
    (c • β).toLinearMap = c • β.toLinearMap := rfl

instance : AddCommMonoid (LieOneCocycle 𝕜 𝓖 𝓐) where
  add_assoc β β' β'' := by
    ext1
    simp only [LieOneCocycle.toLinearMap_add]
    exact add_assoc β.toLinearMap β'.toLinearMap β''.toLinearMap
  zero_add β := by ext1 ; simp
  add_zero β := by ext1 ; simp
  add_comm β β' := by
    ext1
    simp only [LieOneCocycle.toLinearMap_add]
    exact AddCommMagma.add_comm β.toLinearMap β'.toLinearMap
  nsmul n β := { toLinearMap := n • β.toLinearMap }
  nsmul_zero β := by ext1 ; simp only [zero_smul] ; rfl
  nsmul_succ n β := by
    ext1
    simpa only [LieOneCocycle.toLinearMap_add] using succ_nsmul β.toLinearMap n

instance : Module 𝕜 (LieOneCocycle 𝕜 𝓖 𝓐) where
  one_smul β := by ext1 ; simp
  mul_smul c c' β := by ext1 ; simp ; exact mul_smul c c' β.toLinearMap
  smul_zero β := by ext1 ; simp
  smul_add c β β' := by ext1 ; simp
  add_smul c c' β := by ext1 ; simp ; exact Module.add_smul c c' β.toLinearMap
  zero_smul β := by ext1 ; simp

instance : AddCommGroup (LieOneCocycle 𝕜 𝓖 𝓐) where
  zero_add β := AddZeroClass.zero_add β
  add_zero β := AddZeroClass.add_zero β
  nsmul_zero β := zero_nsmul β
  nsmul_succ n β := succ_nsmul β n
  neg β := (-1 : 𝕜) • β
  sub β₁ β₂ := β₁ + (-1 : 𝕜) • β₂
  zsmul k β := (k : 𝕜) • β
  zsmul_zero' β := by simp only [Int.cast_zero, zero_smul]
  zsmul_succ' k β := by simp [add_smul]
  zsmul_neg' k β := by simp [add_smul, smul_smul, add_comm]
  neg_add_cancel β := by
    nth_rewrite 2 [← one_smul 𝕜 β]
    simp only [← add_smul, neg_add_cancel, zero_smul]
  add_comm β₁ β₂ := AddCommMagma.add_comm β₁ β₂

variable {𝕜 𝓖 𝓐}

instance : FunLike (LieOneCocycle 𝕜 𝓖 𝓐) 𝓖 𝓐 where
  coe := fun β X ↦ β.toLinearMap X
  coe_injective' := fun β β' h ↦ by ext1 ; exact LinearMap.ext_iff.mpr (congrFun h)

instance : LinearMapClass (LieOneCocycle 𝕜 𝓖 𝓐) 𝕜 𝓖 𝓐 where
  map_add β X Y := β.toLinearMap.map_add X Y
  map_smulₛₗ β c X := LinearMap.CompatibleSMul.map_smul β.toLinearMap c X

end LieOneCocycle -- namespace

end LieOneCocycle -- section

section LieTwoCocycle

/-! ### Lie algebra 2-cocycles -/

/-- Lie algebra 2-cocycles. -/
@[ext] structure LieTwoCocycle where
  /-- The underlying bilinear map of a Lie algebra 2-cocycle. -/
  toBilin : 𝓖 →ₗ[𝕜] 𝓖 →ₗ[𝕜] 𝓐
  self' : ∀ X, toBilin X X = 0
  leibniz' : ∀ X Y Z, toBilin X ⁅Y, Z⁆ = toBilin ⁅X, Y⁆ Z + toBilin Y ⁅X, Z⁆

namespace LieTwoCocycle

instance : FunLike (LieTwoCocycle 𝕜 𝓖 𝓐) 𝓖 (𝓖 →ₗ[𝕜] 𝓐) where
  coe := fun γ X ↦ LieTwoCocycle.toBilin γ X
  coe_injective' := by
    intro γ γ' h
    ext
    exact congrFun (congrArg DFunLike.coe (congrFun h _)) _

instance : LinearMapClass (LieTwoCocycle 𝕜 𝓖 𝓐) 𝕜 𝓖 (𝓖 →ₗ[𝕜] 𝓐) where
  map_add γ X Y := (LieTwoCocycle.toBilin γ).map_add X Y
  map_smulₛₗ γ c X := (LieTwoCocycle.toBilin γ).map_smul c X

variable {𝕜 𝓖 𝓐}
variable (γ : LieTwoCocycle 𝕜 𝓖 𝓐)

@[simp]
lemma self {X : 𝓖} : γ X X = 0 := γ.self' X

lemma leibniz {X Y Z : 𝓖} : γ X ⁅Y, Z⁆ = γ ⁅X, Y⁆ Z + γ Y ⁅X, Z⁆ := γ.leibniz' X Y Z

lemma apply_add (X₁ X₂ Y : 𝓖) : γ (X₁ + X₂) Y = γ X₁ Y + γ X₂ Y := by simp

lemma apply_add₂ (X Y₁ Y₂ : 𝓖) : γ X (Y₁ + Y₂) = γ X Y₁ + γ X Y₂ := by simp

lemma apply_smul (c : 𝕜) (X Y : 𝓖) : γ (c • X) Y = c • γ X Y := by simp

lemma apply_smul₂ (c : 𝕜) (X Y : 𝓖) : γ X (c • Y) = c • γ X Y := by simp

lemma skew (X Y : 𝓖) : -(γ Y X) = γ X Y := by
  have aux : γ (X + Y) X + γ (X + Y) Y = 0 := by
    rw [← LieTwoCocycle.apply_add₂]
    exact LieTwoCocycle.self γ
  simpa [neg_eq_iff_add_eq_zero] using aux

instance : Zero (LieTwoCocycle 𝕜 𝓖 𝓐) where
  zero := { toBilin := 0 , self' := by simp , leibniz' := by simp }

instance : Add (LieTwoCocycle 𝕜 𝓖 𝓐) where
  add γ γ' :=
    { toBilin := γ.toBilin + γ'.toBilin
      self' := fun X ↦ by simp [γ.self', γ'.self']
      leibniz' := fun X Y Z ↦ by
        simp only [LinearMap.add_apply, γ.leibniz' X Y Z, γ'.leibniz' X Y Z]
        simp only [add_assoc, add_right_inj]
        simp only [← add_assoc, add_left_inj]
        rw [add_comm] }

instance : SMul 𝕜 (LieTwoCocycle 𝕜 𝓖 𝓐) where
  smul c γ :=
    { toBilin := c • γ.toBilin
      self' := fun X ↦ by simp [γ.self']
      leibniz' := fun X Y Z ↦ by simp only [LinearMap.smul_apply, γ.leibniz' X Y Z, smul_add] }

@[simp]
lemma toBilin_zero : (0 : LieTwoCocycle 𝕜 𝓖 𝓐).toBilin = 0 := rfl

@[simp]
lemma toBilin_add (γ γ' : LieTwoCocycle 𝕜 𝓖 𝓐) :
    (γ + γ').toBilin = γ.toBilin + γ'.toBilin := rfl

@[simp]
lemma toBilin_smul (c : 𝕜) (γ : LieTwoCocycle 𝕜 𝓖 𝓐) :
    (c • γ).toBilin = c • γ.toBilin := rfl

instance : AddCommMonoid (LieTwoCocycle 𝕜 𝓖 𝓐) where
  add_assoc γ γ' γ'' := by
    ext1
    simp only [LieTwoCocycle.toBilin_add]
    exact add_assoc _ _ _
  zero_add γ := by ext1 ; simp only [LieTwoCocycle.toBilin_add, add_left_eq_self] ; rfl
  add_zero γ := by ext1 ; simp only [LieTwoCocycle.toBilin_add, add_right_eq_self] ; rfl
  add_comm γ γ' := by ext1 ; simp only [LieTwoCocycle.toBilin_add] ; exact AddCommMagma.add_comm _ _
  nsmul n γ :=
    { toBilin := n • γ.toBilin
      self' := fun X ↦ by simp only [LinearMap.smul_apply, γ.self', smul_zero]
      leibniz' := fun X Y Z ↦ by simp only [LinearMap.smul_apply, γ.leibniz' X Y Z, smul_add] }
  nsmul_zero γ := by ext1 ; simp only [zero_smul] ; rfl
  nsmul_succ n γ := by
    ext1
    simpa only [LieTwoCocycle.toBilin_add] using succ_nsmul γ.toBilin n

instance : Module 𝕜 (LieTwoCocycle 𝕜 𝓖 𝓐) where
  one_smul γ := by ext1 ; simp
  mul_smul c c' γ := by ext1 ; simp ; exact mul_smul c c' γ.toBilin
  smul_zero γ := by ext1 ; simp
  smul_add c γ γ' := by ext1 ; simp
  add_smul c c' γ := by ext1 ; simp ; exact Module.add_smul c c' γ.toBilin
  zero_smul γ := by ext1 ; simp

instance [AddCommGroup 𝓖] [Module 𝕜 𝓖] [LieAlgebra 𝕜 𝓖] [AddCommGroup 𝓐] [Module 𝕜 𝓐] :
    AddCommGroup (LieTwoCocycle 𝕜 𝓖 𝓐) where
  zero_add γ := AddZeroClass.zero_add γ
  add_zero γ := AddZeroClass.add_zero γ
  nsmul_zero γ := zero_nsmul γ
  nsmul_succ n γ := succ_nsmul γ n
  neg γ := (-1 : 𝕜) • γ
  sub γ₁ γ₂ := γ₁ + (-1 : 𝕜) • γ₂
  zsmul k γ := (k : 𝕜) • γ
  zsmul_zero' γ := by simp only [Int.cast_zero, zero_smul]
  zsmul_succ' k γ := by simp [add_smul]
  zsmul_neg' k γ := by simp [add_smul, smul_smul, add_comm]
  neg_add_cancel γ := by
    nth_rewrite 2 [← one_smul 𝕜 γ]
    simp only [← add_smul, neg_add_cancel, zero_smul]
  add_comm γ₁ γ₂ := AddCommMagma.add_comm γ₁ γ₂

lemma add_apply (γ₁ γ₂ : LieTwoCocycle 𝕜 𝓖 𝓐) (X Y : 𝓖) :
    (γ₁ + γ₂) X Y = γ₁ X Y + γ₂ X Y := rfl

lemma smul_apply (c : 𝕜) (γ : LieTwoCocycle 𝕜 𝓖 𝓐) (X Y : 𝓖) :
    (c • γ) X Y = c • γ X Y := rfl

lemma sub_apply (γ₁ γ₂ : LieTwoCocycle 𝕜 𝓖 𝓐) (X Y : 𝓖) :
    (γ₁ - γ₂) X Y = γ₁ X Y - γ₂ X Y := by
  simp only [sub_eq_add_neg, LieTwoCocycle.add_apply]
  rw [show -γ₂ = (-1 : 𝕜) • γ₂ from rfl, LieTwoCocycle.smul_apply]
  simp

@[simp] lemma zero_apply (X Y : 𝓖) : (0 : LieTwoCocycle 𝕜 𝓖 𝓐) X Y = 0 := rfl

@[simp] lemma zero_apply' (X : 𝓖) : (0 : LieTwoCocycle 𝕜 𝓖 𝓐) X = 0 := rfl

end LieTwoCocycle -- namespace

end LieTwoCocycle -- section

section LieTwoCoboundary

/-! ### Lie algebra 2-coboundaries -/

variable {𝕜 𝓖 𝓐}

/-- A Lie algebra 1-cocycle determines a bilinear map via the differential. -/
private def LieOneCocycle.bdry' (β : LieOneCocycle 𝕜 𝓖 𝓐) : 𝓖 →ₗ[𝕜] 𝓖 →ₗ[𝕜] 𝓐 where
  toFun := fun X ↦ β ∘ₗ LieAlgebra.bracketHom 𝕜 𝓖 X
  map_add' X₁ X₂ := by simp_all only [map_add] ; ext ; simp_all
  map_smul' c X := by simp_all only [LinearMapClass.map_smul, RingHom.id_apply] ; ext ; simp_all

/-- A Lie algebra 1-cocycle linearly determines a bilinear map via the differential. -/
private def LieOneCocycle.bdryHom' : LieOneCocycle 𝕜 𝓖 𝓐 →ₗ[𝕜] 𝓖 →ₗ[𝕜] 𝓖 →ₗ[𝕜] 𝓐 where
  toFun := fun β ↦ LieOneCocycle.bdry' β
  map_add' β₁ β₂ := by dsimp ; ext X Y; rfl
  map_smul' c Z := by dsimp ; ext X Y; rfl

/-- The `∂` of a Lie algebra 1-cocycle as a Lie algebra 2-cocycle. -/
def LieOneCocycle.bdry (β : LieOneCocycle 𝕜 𝓖 𝓐) : LieTwoCocycle 𝕜 𝓖 𝓐 where
  toBilin := LieOneCocycle.bdryHom' β
  self' X := by simp [LieOneCocycle.bdryHom', LieOneCocycle.bdry']
  leibniz' X Y Z := by simp [LieOneCocycle.bdryHom', LieOneCocycle.bdry']

variable (𝕜 𝓖 𝓐)

/-- The `∂` as a linear map from Lie algebra 1-cocycles to Lie algebra 2-cocycles. -/
def lieOneCocycle_bdryHom : LieOneCocycle 𝕜 𝓖 𝓐 →ₗ[𝕜] LieTwoCocycle 𝕜 𝓖 𝓐 where
  toFun β := β.bdry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma LieOneCocycle.neg_bdry (β : LieOneCocycle 𝕜 𝓖 𝓐) : (-β).bdry = -β.bdry := by
  change lieOneCocycle_bdryHom 𝕜 𝓖 𝓐 (-β) = -lieOneCocycle_bdryHom 𝕜 𝓖 𝓐 β
  simp

lemma LieOneCocycle.bdry_apply (β : LieOneCocycle 𝕜 𝓖 𝓐) (X Y : 𝓖) :
    β.bdry X Y = β (⁅X, Y⁆) := rfl

/-- Lie algebra 2-coboundaries as a vector space. -/
abbrev LieTwoCoboundary := LinearMap.range (lieOneCocycle_bdryHom 𝕜 𝓖 𝓐)

end LieTwoCoboundary -- section

section LieTwoCohomology

/-! ### Lie algebra 2-cohomology -/

/-- The 2-cohomology `H²(𝓖,𝓐)` of a Lie algebra `𝓖` with coefficients in `𝓐`. -/
def LieTwoCohomology := LieTwoCocycle 𝕜 𝓖 𝓐 ⧸ LieTwoCoboundary 𝕜 𝓖 𝓐

namespace LieTwoCohomology

/-- The 2-cohomology `H²(𝓖,𝓐)` is an additive commutative group. -/
instance : AddCommGroup (LieTwoCohomology 𝕜 𝓖 𝓐) := by
  change AddCommGroup (LieTwoCocycle 𝕜 𝓖 𝓐 ⧸ LieTwoCoboundary 𝕜 𝓖 𝓐)
  exact Submodule.Quotient.addCommGroup (LieTwoCoboundary 𝕜 𝓖 𝓐)

/-- The 2-cohomology `H²(𝓖,𝓐)` is a module over the scalar ring `𝕜`. -/
instance : Module 𝕜 (LieTwoCohomology 𝕜 𝓖 𝓐) := by
  change Module 𝕜 (LieTwoCocycle 𝕜 𝓖 𝓐 ⧸ LieTwoCoboundary 𝕜 𝓖 𝓐)
  exact Submodule.Quotient.module' _

end LieTwoCohomology -- namespace

namespace LieTwoCocycle

/-- The linear map from 2-cocycles to 2-cohomologies of a Lie algebra `𝓖` with coefficients
in `𝓐`. -/
def toLieTwoCohomology : LieTwoCocycle 𝕜 𝓖 𝓐 →ₗ[𝕜] LieTwoCohomology 𝕜 𝓖 𝓐 :=
  (LieTwoCoboundary 𝕜 𝓖 𝓐).mkQ

lemma range_toLieTwoCohomology_eq_top :
    LinearMap.range (toLieTwoCohomology 𝕜 𝓖 𝓐) = ⊤ :=
  Submodule.range_mkQ ..

variable {𝕜 𝓖 𝓐}

/-- The projection to 2-cohomologies from 2-cocycles of a Lie algebra `𝓖` with coefficients
in `𝓐`. (This definition is to enable dot notation, while the linear map version doesn't.) -/
def cohomologyClass (γ : LieTwoCocycle 𝕜 𝓖 𝓐) : LieTwoCohomology 𝕜 𝓖 𝓐 :=
  LieTwoCocycle.toLieTwoCohomology _ _ _ γ

/-- Adding a coboundary does not change the cohomology class. -/
lemma cohomologyClass_add_bdry (γ : LieTwoCocycle 𝕜 𝓖 𝓐) (β : LieOneCocycle 𝕜 𝓖 𝓐) :
    (γ + β.bdry).cohomologyClass = γ.cohomologyClass := by
  simp only [cohomologyClass, map_add, add_right_eq_self]
  apply (Submodule.Quotient.mk_eq_zero _).mpr <| LinearMap.mem_range.mpr ⟨β, rfl⟩

/-- A cocycle representing a trivial cohomology class is a coboundary. -/
lemma exists_eq_bdry (hγ : γ.cohomologyClass = 0) :
    ∃ β : LieOneCocycle 𝕜 𝓖 𝓐, γ = β.bdry := by
  simp_rw [@Eq.comm (LieTwoCocycle 𝕜 𝓖 𝓐) γ _]
  simpa using (Submodule.Quotient.eq _).mp <|
    show γ.cohomologyClass = LieTwoCocycle.cohomologyClass 0 by rw [hγ] ; rfl

end LieTwoCocycle -- namespace

end LieTwoCohomology -- section

section IsLieAbelian

variable [IsLieAbelian 𝓖]

variable {𝕜 𝓖 𝓐}

/-- For abelian Lie algebras, a 2-coboundary is necessarily zero. -/
lemma LieOneCocycle.bdry_apply_eq_zero_of_isLieAbelian (β : LieOneCocycle 𝕜 𝓖 𝓐) (X Y : 𝓖) :
    β.bdry X Y = 0 := by
  simp [LieOneCocycle.bdry_apply]

variable (𝕜 𝓖 𝓐)

/-- For abelian Lie algebras, the space of 2-coboundaries is the zero vector space. -/
lemma LieTwoCoboundary.eq_bot_of_isLieAbelian :
    LieTwoCoboundary 𝕜 𝓖 𝓐 = ⊥ := by
  refine LinearMap.range_eq_bot.mpr ?_
  ext β X Y
  exact β.bdry_apply_eq_zero_of_isLieAbelian X Y

/-- For abelian Lie algebras, the map from 2-cocycles to their cohomology classes has
trivial kernel. -/
lemma LieTwoCocycle.ker_toLieTwoCohomology_eq_bot_of_isLieAbelian :
    LinearMap.ker (LieTwoCocycle.toLieTwoCohomology 𝕜 𝓖 𝓐) = ⊥ := by
  rw [LieTwoCocycle.toLieTwoCohomology, Submodule.ker_mkQ]
  exact LieTwoCoboundary.eq_bot_of_isLieAbelian 𝕜 𝓖 𝓐

/-- For abelian Lie algebras, the map from 2-cocycles to their cohomology classes is a linear
equivalence. -/
noncomputable def LieTwoCocycle.toLieTwoCohomologyEquiv :
    LieTwoCocycle 𝕜 𝓖 𝓐 ≃ₗ[𝕜] LieTwoCohomology 𝕜 𝓖 𝓐 :=
  LinearEquiv.ofBijective (LieTwoCocycle.toLieTwoCohomology 𝕜 𝓖 𝓐)
    ⟨LinearMap.ker_eq_bot.mp <| ker_toLieTwoCohomology_eq_bot_of_isLieAbelian ..,
     LinearMap.range_eq_top.mp <| range_toLieTwoCohomology_eq_top ..⟩

lemma LieTwoCocycle.toLieTwoCohomologyEquiv_toLinearMap :
    (toLieTwoCohomologyEquiv 𝕜 𝓖 𝓐).toLinearMap = toLieTwoCohomology 𝕜 𝓖 𝓐 := rfl

end IsLieAbelian --section

end VirasoroProject -- namespace
