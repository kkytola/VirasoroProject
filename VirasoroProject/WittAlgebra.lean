/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.LinearAlgebra.Basis.Bilinear
import VirasoroProject.CyclicTripleSum
import VirasoroProject.ToMathlib.LinearAlgebra.Basis.Defs

/-!
# Witt algebra

This file defines the Witt algebra, an infinite-dimensional Lie algebra.
A few assumptions are made of the ground ring `𝕜`, mainly that it is of characteristic zero.

Typical interpretations of the Witt algebra are the following:
 * In the case that the ground field is the real numbers, `𝕜 = ℝ`, the Witt algebra is the Lie
   algebra of polynomial vector fields on the circle.
 * In the case that the ground field is the complex numbers, `𝕜 = ℂ`, the Witt algebra is the
   Lie algebra of meromorphic vector fields on the Riemann sphere with poles only at 0 and ∞.

## Main definitions

* ...
* ...

## Main statements

* ...

* ...

## Implementation notes

We define the Witt algebra based on an explicit basis indexed by the integers `ℤ`. This should be
the most basic implementation.

TODO: Prove that the Witt algebra is isomorphic, e.g., to the Lie algebra of meromorphic vector
fields on the Riemann sphere with poles only at 0 and ∞. (This of course needs some amount of
differential geometry to be added to Lean.)

## Tags

Witt algebra

-/

namespace VirasoroProject

variable (𝕜 : Type*) [CommRing 𝕜]

/-- The Witt algebra: an ∞-dimensional Lie algebra (polynomial vector fields on a circle). -/
def WittAlgebra := ℤ →₀ 𝕜

noncomputable instance : AddCommGroup (WittAlgebra 𝕜) := Finsupp.instAddCommGroup

noncomputable instance : Module 𝕜 (WittAlgebra 𝕜) := Finsupp.module ..

namespace WittAlgebra

/-- The basis of `ℓₙ` generators of the Witt algebra (indices `n : ℤ`). -/
def lgen : Basis ℤ 𝕜 (WittAlgebra 𝕜) := Finsupp.basisFun _ _

lemma lgen_eq_single (n : ℤ) : lgen 𝕜 n = Finsupp.single n 1 := rfl

/-- The Lie bracket for the Witt algebra `WittAlgebra` as a bilinear map. -/
noncomputable def bracket :
    (WittAlgebra 𝕜) →ₗ[𝕜] (WittAlgebra 𝕜) →ₗ[𝕜] (WittAlgebra 𝕜) :=
  (lgen 𝕜).constr 𝕜 <| fun n ↦ (lgen 𝕜).constr 𝕜 <| fun m ↦ (n - m : 𝕜) • lgen 𝕜 (n + m)

/-- `⁅ℓ(n), ℓ(m)⁆ = (n-m) • ℓ(n+m)` in `WittAlgebra`. -/
@[simp]
lemma bracket_lgen_lgen' (n m : ℤ) :
    bracket 𝕜 (lgen 𝕜 n) (lgen 𝕜 m) = (n - m : 𝕜) • lgen 𝕜 (n + m) := by
  simp only [bracket, Basis.constr_basis]

lemma bracket_eq_neg_flip :
    bracket 𝕜 = -(bracket 𝕜).flip := by
  apply LinearMap.ext_basis (lgen _) (lgen _)
  intro n m
  simp [add_comm m, ← neg_smul, neg_sub]

variable {𝕜}

/-- Antisymmetry of the Lie bracket of the Witt algebra `WittAlgebra`. -/
lemma bracket_antisymm (X Y : WittAlgebra 𝕜) :
    bracket 𝕜 X Y = - bracket 𝕜 Y X := by
  simpa using LinearMap.congr_fun (LinearMap.congr_fun (bracket_eq_neg_flip 𝕜) X) Y

/-- Antisymmetry (`⁅X, X⁆ = 0` form) of the Lie bracket of the Witt algebra `WittAlgebra`. -/
lemma bracket_self [CharZero 𝕜] [NoZeroSMulDivisors 𝕜 (WittAlgebra 𝕜)] (X : WittAlgebra 𝕜) :
    bracket 𝕜 X X = 0 := by
  have aux : (2 : 𝕜) • bracket 𝕜 X X = 0 := by
    have obs := congr_arg (· + bracket 𝕜 X X) (bracket_antisymm X X)
    simp only [neg_add_cancel] at obs
    rwa [← one_smul 𝕜 (bracket 𝕜 X X), ← add_smul, one_add_one_eq_two] at obs
  simpa only [OfNat.ofNat_ne_zero, false_or] using eq_zero_or_eq_zero_of_smul_eq_zero aux

variable (𝕜)

/-- The Jacobi identity of the Lie bracket of the Witt algebra `WittAlgebra`. -/
lemma bracketCyclic_eq_zero :
    cyclicTripleSumHom (bracket 𝕜) (bracket 𝕜) = 0 := by
  apply LinearMap.ext_basis (lgen _) (lgen _)
  intro n m
  apply (lgen _).ext
  intro k
  simp only [cyclicTripleSumHom_apply, LinearMap.coe_mk, AddHom.coe_mk, bracket_lgen_lgen',
             LinearMapClass.map_smul, Int.cast_add, LinearMap.zero_apply, smul_smul]
  rw [show n + (m + k) = n + m + k by ring,
      show m + (k + n) = n + m + k by ring,
      show k + (n + m) = n + m + k by ring]
  simp only [← add_smul]
  convert zero_smul 𝕜 ((lgen 𝕜) (n + m + k))
  ring

variable {𝕜}

/-- The Leibniz property (Jacobi identity) of the Lie bracket of the Witt algebra `WittAlgebra`. -/
lemma bracket_leibniz (X Y Z : WittAlgebra 𝕜) :
    bracket 𝕜 X (bracket 𝕜 Y Z) =
      bracket 𝕜 (bracket 𝕜 X Y) Z + bracket 𝕜 Y (bracket 𝕜 X Z) := by
  have key := LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun
                (bracketCyclic_eq_zero 𝕜) X) Y) Z
  simp only [cyclicTripleSumHom_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at key
  rw [add_assoc (bracket 𝕜 X _)] at key
  rw [eq_neg_of_add_eq_zero_left key]
  rw [bracket_antisymm Z X, bracket_antisymm Z _]
  simp

variable [CharZero 𝕜] [NoZeroSMulDivisors 𝕜 (WittAlgebra 𝕜)]

/-- The Lie ring structure on the Witt algebra `WittAlgebra`. -/
noncomputable instance : LieRing (WittAlgebra 𝕜) where
  bracket X Y := bracket _ X Y
  add_lie X₁ X₂ Y := by simp only [bracket, map_add, LinearMap.add_apply]
  lie_add X Y₁ Y₂ := by simp only [map_add]
  lie_self X := bracket_self X
  leibniz_lie X Y Z := bracket_leibniz X Y Z

/-- The Lie algebra structure on the Witt algebra `WittAlgebra`. -/
noncomputable instance : LieAlgebra 𝕜 (WittAlgebra 𝕜) where
  lie_smul c X Y := map_smul (bracket 𝕜 X) c Y

variable (𝕜)

/-- `⁅ℓ(n), ℓ(m)⁆ = (n-m) • ℓ(n+m)` in `WittAlgebra`. -/
@[simp]
lemma bracket_lgen_lgen (n m : ℤ) :
    ⁅lgen 𝕜 n, lgen 𝕜 m⁆ = (n - m : 𝕜) • lgen 𝕜 (n + m) :=
  bracket_lgen_lgen' 𝕜 n m

end WittAlgebra -- namespace

end VirasoroProject -- namespace
