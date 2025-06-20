/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.Lie.OfAssociative
import VirasoroProject.Commutator
import VirasoroProject.ToMathlib.Algebra.Lie.Basic

/-!
# Constructing representations of Lie algebras from operators corresponding to a basis

This file contains a construction of a Lie algebra representation from a basis and operators
satisfying the corresponding commutation relations. (It is used in particular in the Sugawara
constructions.)

## Main definitions

* `LieAlgebra.representationOfBasis`: Given a basis `B` of a Lie algebra `𝓖` and a collection of
  linear operators on a vector space `V` satisfying the commutation relations specified by the Lie
  brackets of the basis elements, construct a representation of `𝓖` on the vector space `V`.

-/


namespace LieAlgebra

section representation

/-- A representation of a `𝕜`-Lie algebra `𝓖` on a `𝕂`-vector space `V`. -/
abbrev Representation (𝕜 𝕂 : Type*) [CommRing 𝕜] [CommRing 𝕂]
    (𝓖 : Type*) [LieRing 𝓖] [LieAlgebra 𝕜 𝓖]
    (V : Type*) [AddCommGroup V] [Module 𝕂 V] [Module 𝕜 V]
    [SMul 𝕜 𝕂] [IsScalarTower 𝕜 𝕂 V] [SMulCommClass 𝕂 𝕜 V] :=
    𝓖 →ₗ⁅𝕜⁆ V →ₗ[𝕂] V

lemma Representation.apply_bracket_eq_commutator {𝕜 𝕂 : Type*} [CommRing 𝕜] [CommRing 𝕂]
    {𝓖 : Type*} [LieRing 𝓖] [LieAlgebra 𝕜 𝓖]
    {V : Type*} [AddCommGroup V] [Module 𝕂 V] [Module 𝕜 V]
    [SMul 𝕜 𝕂] [IsScalarTower 𝕜 𝕂 V] [SMulCommClass 𝕂 𝕜 V]
    (ρ : Representation 𝕜 𝕂 𝓖 V) (X Y : 𝓖) :
    ρ ⁅X, Y⁆ = (ρ X).commutator (ρ Y) := by
  simp [LinearMap.commutator]
  rfl

-- TODO: Generalize so that the two fields can be different.
/-- An auxiliary definition for constructing representation of Lie algebras from a basis and a
corresponding collection of operators; `representationOfBasisAux` is just a linear map from
the Lie algebra to the space of operators (not yet a morphism of Lie algebras). -/
noncomputable def representationOfBasisAux
    {𝕂 : Type*} [Field 𝕂] {V : Type*} [AddCommGroup V] [Module 𝕂 V]
    {𝓖 : Type*} [LieRing 𝓖] [LieAlgebra 𝕂 𝓖] {ι : Type*} (B : Basis ι 𝕂 𝓖)
    (genOper : ι → (V →ₗ[𝕂] V)) :
    𝓖 →ₗ[𝕂] V →ₗ[𝕂] V :=
  B.constr 𝕂 <| fun i ↦ genOper i

@[simp] lemma representationOfBasisAux_apply_basis
    {𝕂 : Type*} [Field 𝕂] {V : Type*} [AddCommGroup V] [Module 𝕂 V]
    {𝓖 : Type*} [LieRing 𝓖] [LieAlgebra 𝕂 𝓖] {ι : Type*} (B : Basis ι 𝕂 𝓖)
    (genOper : ι → (V →ₗ[𝕂] V)) (i : ι) :
    LieAlgebra.representationOfBasisAux B genOper (B i) = genOper i := by
  simp [LieAlgebra.representationOfBasisAux]

lemma representationOfBasisAux_property
    {𝕂 : Type*} [Field 𝕂] {V : Type*} [AddCommGroup V] [Module 𝕂 V]
    {𝓖 : Type*} [LieRing 𝓖] [LieAlgebra 𝕂 𝓖] {ι : Type*} (B : Basis ι 𝕂 𝓖)
    {genOper : ι → (V →ₗ[𝕂] V)}
    (genComm : ∀ i j, (genOper i).commutator (genOper j)
      = LieAlgebra.representationOfBasisAux B genOper ⁅B i, B j⁆) :
    (LieAlgebra.representationOfBasisAux B genOper).compRight.comp (LieAlgebra.bracketHom 𝕂 𝓖)
      = (LinearMap.commutatorBilin V).compl₁₂
          (LieAlgebra.representationOfBasisAux B genOper)
          (LieAlgebra.representationOfBasisAux B genOper) :=
  B.ext fun i ↦ B.ext fun j ↦ by simp [genComm i j]

/-- A representation of a Lie algebra `𝓖` with basis `B` constructed from a collection of operators
satisfying the commutation relations specified by the Lie brackets of the basis elements. -/
noncomputable def representationOfBasis
    {𝕂 : Type*} [Field 𝕂] {V : Type*} [AddCommGroup V] [Module 𝕂 V]
    {𝓖 : Type*} [LieRing 𝓖] [LieAlgebra 𝕂 𝓖] {ι : Type*} (B : Basis ι 𝕂 𝓖)
    {genOper : ι → (V →ₗ[𝕂] V)}
    (genComm : ∀ i j, (genOper i).commutator (genOper j)
      = LieAlgebra.representationOfBasisAux B genOper ⁅B i, B j⁆) :
    Representation 𝕂 𝕂 𝓖 V where
  toFun := LieAlgebra.representationOfBasisAux B genOper
  map_add' := by simp
  map_smul' := by simp
  map_lie' := by
    intro X Y
    have key := LieAlgebra.representationOfBasisAux_property B genComm
    exact LinearMap.congr_fun (LinearMap.congr_fun key X) Y

end representation

lemma representationOfBasis_property
    {𝕂 : Type*} [Field 𝕂] {V : Type*} [AddCommGroup V] [Module 𝕂 V]
    {𝓖 : Type*} [LieRing 𝓖] [LieAlgebra 𝕂 𝓖] {ι : Type*} (B : Basis ι 𝕂 𝓖)
    {genOper : ι → (V →ₗ[𝕂] V)}
    (genComm : ∀ i j, (genOper i).commutator (genOper j)
      = LieAlgebra.representationOfBasisAux B genOper ⁅B i, B j⁆) :
    (LieAlgebra.representationOfBasis B genComm).compRight.comp (LieAlgebra.bracketHom 𝕂 𝓖)
      = (LinearMap.commutatorBilin V).compl₁₂
          (LieAlgebra.representationOfBasis B genComm)
          (LieAlgebra.representationOfBasis B genComm) := by
  exact representationOfBasisAux_property B genComm

end LieAlgebra -- namespace
