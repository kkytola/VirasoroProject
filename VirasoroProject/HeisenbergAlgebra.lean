/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.LinearAlgebra.Basis.Bilinear
import VirasoroProject.IsCentralExtension
import VirasoroProject.ToMathlib.Algebra.Lie.Abelian
import VirasoroProject.ToMathlib.LinearAlgebra.Basis.Defs

/-!
# Heisenberg algebra

This file defines the Heisenberg algebra, as the one-dimensional central extension of a countably
infinite dimensional abelian Lie algebra associated to a nontrivial 2-cocycle.

(The construction is mathematically boring, but the interesting part is the relation with
Virasoro algebra: suitable positive energy representations of the Heisenberg algebra can be made
into representations of the Virasoro algebra by a Sugawara construction.)

## Main definitions

* `HeisenbergAlgebra`: The Heisenberg algebra.
* `HeisenbergAlgebra.jgen`: The (commonly used) elements Jₖ, k ∈ ℤ, of the Heisenberg algebra.
* `HeisenbergAlgebra.kgen`: The central element K of the Heisenberg algebra (commonly set
  to 1 in representations).

## Main statements

* `HeisenbergAlgebra.instLieAlgebra`: The Heisenberg algebra is a Lie algebra.

## Implementation notes

The Heisenberg algebra is defined as a central extension of an infinite-dimensional abelian Lie
algebra. (A more direct definition based on defining a Lie bracket on a countably infinite
dimensional vector space would also be possible.)

## Tags

Heisenberg algebra

-/

namespace VirasoroProject

section AbelianLieAlgebraOn

/-! ### Abelian Lie algebra with a given basis -/

variable (ι : Type*)
variable (𝕜 : Type*) [CommRing 𝕜]

/-- An auxiliary construction of an abelian Lie algebra with a given index set for a basis. -/
def AbelianLieAlgebraOn := ι →₀ 𝕜

noncomputable instance : AddCommGroup (AbelianLieAlgebraOn ι 𝕜) := Finsupp.instAddCommGroup

noncomputable instance : Module 𝕜 (AbelianLieAlgebraOn ι 𝕜) := Finsupp.module ..

namespace AbelianLieAlgebraOn

variable {ι}

/-- The basis of `jᵢ` generators of the abelian Lie algebra (indices `i : ι`). -/
noncomputable def jgen : Basis ι 𝕜 (AbelianLieAlgebraOn ι 𝕜) := Finsupp.basisFun _ _

lemma jgen_eq_single (i : ι) : jgen 𝕜 i = Finsupp.single i 1 := rfl

/-- The Lie ring structure on the Witt algebra `WittAlgebra`. -/
noncomputable instance : LieRing (AbelianLieAlgebraOn ι 𝕜) where
  bracket X Y := 0
  add_lie X₁ X₂ Y := by simp
  lie_add X Y₁ Y₂ := by simp
  lie_self X := by simp
  leibniz_lie X Y Z := by simp

@[simp] lemma lie_def (X Y : AbelianLieAlgebraOn ι 𝕜) : ⁅X, Y⁆ = 0 := rfl

/-- The Lie algebra structure on the Witt algebra `WittAlgebra`. -/
noncomputable instance : LieAlgebra 𝕜 (AbelianLieAlgebraOn ι 𝕜) where
  lie_smul c X Y := by simp

instance : IsLieAbelian (AbelianLieAlgebraOn ι 𝕜) where
  trivial _ _ := rfl

end AbelianLieAlgebraOn -- namespace

end AbelianLieAlgebraOn -- section

section HeisenbergCocycle

/-! ### The 2-cocycle defining the Heisenberg algebra as central extension -/

namespace AbelianLieAlgebraOn

variable (𝕜 : Type*) [Field 𝕜]

/-- A bilinear map version of the Heisenberg cocycle. -/
noncomputable def heisenbergCocycleBilin : (AbelianLieAlgebraOn ℤ 𝕜) →ₗ[𝕜] (AbelianLieAlgebraOn ℤ 𝕜) →ₗ[𝕜] 𝕜 :=
  (jgen 𝕜).constr 𝕜 <| fun k ↦ (jgen 𝕜).constr 𝕜 <| fun l ↦
      if k + l = 0 then k else 0

lemma heisenbergCocycleBilin_apply_jgen_jgen (k l : ℤ) :
    heisenbergCocycleBilin 𝕜 (jgen 𝕜 k) (jgen 𝕜 l)
      = if k + l = 0 then k else 0 := by
  simp [heisenbergCocycleBilin]

example (R U V W : Type) [Field R] [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module R U] [Module R V] [Module R W] (β : U →ₗ[R] V →ₗ[R] W) :
    V →ₗ[R] U →ₗ[R] W := by
  exact β.flip

lemma heisenbergCocycleBilin_eq_neg_flip :
    heisenbergCocycleBilin 𝕜 = -(heisenbergCocycleBilin 𝕜).flip := by
  apply LinearMap.ext_basis (jgen _) (jgen _)
  intro k l
  simp only [heisenbergCocycleBilin, Basis.constr_basis, LinearMap.neg_apply, LinearMap.flip_apply]
  by_cases opp : k + l = 0
  · simp [↓reduceIte, show l = -k by linarith]
  · simp [opp, add_comm l k]

variable [CharZero 𝕜]

/-- The Heisenberg cocycle. -/
noncomputable def heisenbergCocycle :
    LieTwoCocycle 𝕜 (AbelianLieAlgebraOn ℤ 𝕜) 𝕜 where
  toBilin := heisenbergCocycleBilin 𝕜
  self' X := by
    apply (self_eq_neg 𝕜 𝕜).mp
    simpa only [LinearMap.neg_apply, LinearMap.coe_mk, AddHom.coe_mk]
      using LinearMap.congr_fun₂ (heisenbergCocycleBilin_eq_neg_flip 𝕜) X X
  leibniz' X Y Z := by
    simp only [lie_def, map_zero, LinearMap.zero_apply, (lie_skew X Z).symm, neg_zero, add_zero]

lemma heisenbergCocycle_apply_jgen_jgen (k l : ℤ) :
    heisenbergCocycle 𝕜 (jgen 𝕜 k) (jgen 𝕜 l) = if k + l = 0 then k else 0 :=
  heisenbergCocycleBilin_apply_jgen_jgen 𝕜 k l

lemma heisenbergCocycle_ne_zero :
    heisenbergCocycle 𝕜 ≠ 0 := by
  have obs := heisenbergCocycle_apply_jgen_jgen 𝕜 1 (-1)
  simp only [Int.reduceNeg, add_neg_cancel, ↓reduceIte, Int.cast_one] at obs
  intro maybe_zero
  simp [maybe_zero] at obs

/-- The Heisenberg cocycle is cohomologically nontrivial. -/
theorem cohomologyClass_heisenbergCocycle_ne_zero :
    (heisenbergCocycle 𝕜).cohomologyClass ≠ 0 := by
  change LieTwoCocycle.toLieTwoCohomologyEquiv 𝕜
    (AbelianLieAlgebraOn ℤ 𝕜) 𝕜 (heisenbergCocycle 𝕜) ≠ 0
  exact (LinearEquiv.map_ne_zero_iff _).mpr <| heisenbergCocycle_ne_zero 𝕜

/-- The abelian Lie algebra 2-cohomology `H²(AbelianLieAlgebraOn ℤ 𝕜, 𝕜)` is nontrivial. -/
theorem nontrivial_lieTwoCohomology :
    Nontrivial (LieTwoCohomology 𝕜 (AbelianLieAlgebraOn ℤ 𝕜) 𝕜) :=
  nontrivial_of_ne _ _ (cohomologyClass_heisenbergCocycle_ne_zero 𝕜)

end AbelianLieAlgebraOn -- namespace

end HeisenbergCocycle -- section

section HeisenbergAlgebra

/-! ### The Heisenberg (Lie) algebra -/

variable (𝕜 : Type*) [Field 𝕜]
variable [CharZero 𝕜]

/-- The Heisenberg algebra. -/
def HeisenbergAlgebra := LieTwoCocycle.CentralExtension (AbelianLieAlgebraOn.heisenbergCocycle 𝕜)

namespace HeisenbergAlgebra

lemma ext' {X Y : HeisenbergAlgebra 𝕜} (h₁ : X.1 = Y.1) (h₂ : X.2 = Y.2) :
    X = Y :=
  LieTwoCocycle.CentralExtension.ext h₁ h₂

/-- The Heisenberg algebra is a Lie ring. -/
noncomputable instance : LieRing (HeisenbergAlgebra 𝕜) :=
  LieTwoCocycle.CentralExtension.instLieRing _

/-- The Heisenberg algebra is a Lie algebra. -/
noncomputable instance : LieAlgebra 𝕜 (HeisenbergAlgebra 𝕜) :=
  LieTwoCocycle.CentralExtension.instLieAlgebra _

variable {𝕜}

/-- The projection from Heisenberg algebra to the original abelian Lie algebra. -/
noncomputable def toAbelianLieAlgebraOn : HeisenbergAlgebra 𝕜 →ₗ⁅𝕜⁆ AbelianLieAlgebraOn ℤ 𝕜 :=
  LieTwoCocycle.CentralExtension.proj (AbelianLieAlgebraOn.heisenbergCocycle 𝕜)

variable (𝕜)

/-- The embedding of central elements to Heisenberg algebra. -/
noncomputable def ofCentral : 𝕜 →ₗ⁅𝕜⁆ HeisenbergAlgebra 𝕜 :=
  LieTwoCocycle.CentralExtension.emb (AbelianLieAlgebraOn.heisenbergCocycle 𝕜)

lemma bracket_def' (X Y : HeisenbergAlgebra 𝕜) :
    ⁅X, Y⁆ = ⟨⁅toAbelianLieAlgebraOn X, toAbelianLieAlgebraOn Y⁆,
              (AbelianLieAlgebraOn.heisenbergCocycle 𝕜) (toAbelianLieAlgebraOn X) (toAbelianLieAlgebraOn Y)⟩ := by
  rfl

@[simp] lemma bracket_fst (X Y : HeisenbergAlgebra 𝕜) :
    ⁅X, Y⁆.1 = 0 := rfl

@[simp] lemma bracket_snd (X Y : HeisenbergAlgebra 𝕜) :
    ⁅X, Y⁆.2 = (AbelianLieAlgebraOn.heisenbergCocycle 𝕜) (toAbelianLieAlgebraOn X) (toAbelianLieAlgebraOn Y) := rfl

lemma add_def' (X Y : HeisenbergAlgebra 𝕜) :
    X + Y = ⟨X.1 + Y.1, X.2 + Y.2⟩ := rfl

lemma smul_def' (c : 𝕜) (X : HeisenbergAlgebra 𝕜) :
    c • X = ⟨c • X.1, c * X.2⟩ := rfl

@[simp] lemma add_fst (X Y : HeisenbergAlgebra 𝕜) :
    (X + Y).1 = X.1 + Y.1 := rfl

@[simp] lemma add_snd (X Y : HeisenbergAlgebra 𝕜) :
    (X + Y).2 = X.2 + Y.2 := rfl

@[simp] lemma smul_fst (c : 𝕜) (X : HeisenbergAlgebra 𝕜) :
    (c • X).1 = c • X.1 := rfl

@[simp] lemma smul_snd (c : 𝕜) (X : HeisenbergAlgebra 𝕜) :
    (c • X).2 = c * X.2 := rfl

/-- The Heisenberg algebra is a central extension of the Witt algebra. -/
instance isCentralExtension : LieAlgebra.IsCentralExtension (ofCentral 𝕜) toAbelianLieAlgebraOn :=
  LieTwoCocycle.CentralExtension.isCentralExtension _

/-- The (commonly used) `Jₖ` elements of the Heisenberg algebra, for `k ∈ ℤ`. -/
noncomputable def jgen (k : ℤ) : HeisenbergAlgebra 𝕜 := ⟨.jgen 𝕜 k, 0⟩

/-- The `K` central element of the Heisenberg algebra, which is commonly set to 1 (in
representations). -/
noncomputable def kgen : HeisenbergAlgebra 𝕜 := ofCentral 𝕜 1

lemma kgen_eq_ofCentral_one : kgen 𝕜 = ofCentral 𝕜 1 := rfl

lemma kgen_eq' : kgen 𝕜 = ⟨0, 1⟩ := rfl

lemma jgen_eq' (k : ℤ) : jgen 𝕜 k = ⟨.jgen 𝕜 k, 0⟩ := rfl

@[simp] lemma ofCentral_apply (a : 𝕜) : ofCentral 𝕜 a = a • (kgen 𝕜) := by
  change (⟨0, a⟩ : HeisenbergAlgebra 𝕜) = a • ⟨0, 1⟩
  aesop

lemma toAbelianLieAlgebraOn_kgen :
  toAbelianLieAlgebraOn (kgen 𝕜) = 0 := rfl

@[simp] lemma toAbelianLieAlgebraOn_jgen (n : ℤ) :
  toAbelianLieAlgebraOn (jgen 𝕜 n) = AbelianLieAlgebraOn.jgen 𝕜 n := rfl

@[simp] lemma kgen_bracket (Z : HeisenbergAlgebra 𝕜) :
    ⁅kgen 𝕜, Z⁆ = 0 :=
  (isCentralExtension 𝕜).central 1 Z

@[simp] lemma jgen_bracket (k l : ℤ) :
    ⁅jgen 𝕜 k, jgen 𝕜 l⁆ = if k + l = 0 then (k : 𝕜) • kgen 𝕜 else 0 := by
  simp_rw [bracket_def']
  by_cases h : k + l = 0
  · simp [h]
    apply ext'
    · simp [kgen_eq']
    · simp [AbelianLieAlgebraOn.heisenbergCocycle_apply_jgen_jgen, kgen_eq', h]
  · simp [h]
    apply ext' <;> simp [AbelianLieAlgebraOn.heisenbergCocycle_apply_jgen_jgen, h]

/-- A section of the standard projection from the Heisenberg algebra to the underlying
abelian Lie algebra. -/
noncomputable def jsection : AbelianLieAlgebraOn ℤ 𝕜 →ₗ[𝕜] HeisenbergAlgebra 𝕜 :=
  LieTwoCocycle.CentralExtension.stdSection (AbelianLieAlgebraOn.heisenbergCocycle 𝕜)

@[simp] lemma jsection_jgen (l : ℤ) :
    jsection 𝕜 (AbelianLieAlgebraOn.jgen 𝕜 l) = jgen 𝕜 l :=
  rfl

/-- The most commonly used basis of the Heisenberg algebra, consisting of `Jₖ` (`k ∈ ℤ`)
and the central element `K`. -/
noncomputable def basisJK : Basis (Option ℤ) 𝕜 (HeisenbergAlgebra 𝕜) :=
  ((isCentralExtension 𝕜).basis (jsection 𝕜) rfl
        (Basis.singleton Unit 𝕜) (AbelianLieAlgebraOn.jgen 𝕜)).reindex
    { toFun uz := match uz with
        | Sum.inl _ => none
        | Sum.inr l => some l
      invFun oz := match oz with
        | none => Sum.inl ⟨⟩
        | some l => Sum.inr l
      left_inv uz := match uz with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      right_inv oz := match oz with
        | none => rfl
        | some _ => rfl }

@[simp] lemma basisJK_some (l : ℤ) :
    basisJK 𝕜 (some l) = jgen 𝕜 l := by
  simp [basisJK]

@[simp] lemma basisJK_none :
    basisJK 𝕜 none = kgen 𝕜 := by
  simp [basisJK]

end HeisenbergAlgebra -- namespace

end HeisenbergAlgebra

end VirasoroProject -- namespace
