/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import VirasoroProject.IsCentralExtension
import VirasoroProject.ToMathlib.Algebra.Lie.Abelian
import VirasoroProject.VirasoroCocycle

/-!
# The Virasoro algebra

This file defines the Virasoro algebra, an infinite-dimensional Lie algebra which is the unique
one-dimensional central extension of the Witt algebra.

(In two-dimensional conformal field theory (CFT), the Virasoro algebra describes the effects of
infinitesimal conformal transformations on the state space of the theory, or equivalently on its
space of local fields.)

## Main definitions

* ...
* ...

## Main statements

* ...

* ...

## Implementation notes

## Tags

Virasoro algebra

-/

namespace VirasoroProject

section VirasoroAlgebra

/-! ### The Virasoro algebra -/

variable (𝕜 : Type*) [Field 𝕜]
variable [CharZero 𝕜]

/-- The Virasoro algebra. -/
def VirasoroAlgebra := LieTwoCocycle.CentralExtension (WittAlgebra.virasoroCocycle 𝕜)

namespace VirasoroAlgebra

private lemma ext' {X Y : VirasoroAlgebra 𝕜} (h₁ : X.1 = Y.1) (h₂ : X.2 = Y.2) :
    X = Y :=
  LieTwoCocycle.CentralExtension.ext h₁ h₂

/-- The Virasoro algebra is a Lie ring. -/
noncomputable instance : LieRing (VirasoroAlgebra 𝕜) :=
  LieTwoCocycle.CentralExtension.instLieRing _

/-- The Virasoro algebra is a Lie algebra. -/
noncomputable instance : LieAlgebra 𝕜 (VirasoroAlgebra 𝕜) :=
  LieTwoCocycle.CentralExtension.instLieAlgebra _

variable {𝕜}

/-- The projection from Virasoro algebra to Witt algebra. -/
def toWittAlgebra : VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ WittAlgebra 𝕜 :=
  LieTwoCocycle.CentralExtension.proj (WittAlgebra.virasoroCocycle 𝕜)

variable (𝕜)

/-- The embedding of central elements to Virasoro algebra. -/
noncomputable def ofCentral : 𝕜 →ₗ⁅𝕜⁆ VirasoroAlgebra 𝕜 :=
  LieTwoCocycle.CentralExtension.emb (WittAlgebra.virasoroCocycle 𝕜)

private lemma bracket_def' (X Y : VirasoroAlgebra 𝕜) :
    ⁅X, Y⁆ = ⟨⁅toWittAlgebra X, toWittAlgebra Y⁆,
              (WittAlgebra.virasoroCocycle 𝕜) (toWittAlgebra X) (toWittAlgebra Y)⟩ := by
  rfl

@[simp] private lemma bracket_fst (X Y : VirasoroAlgebra 𝕜) :
    ⁅X, Y⁆.1 = ⁅toWittAlgebra X, toWittAlgebra Y⁆ := rfl

@[simp] private lemma bracket_snd (X Y : VirasoroAlgebra 𝕜) :
    ⁅X, Y⁆.2 = (WittAlgebra.virasoroCocycle 𝕜) (toWittAlgebra X) (toWittAlgebra Y) := rfl

private lemma add_def' (X Y : VirasoroAlgebra 𝕜) :
    X + Y = ⟨X.1 + Y.1, X.2 + Y.2⟩ := rfl

private lemma smul_def' (c : 𝕜) (X : VirasoroAlgebra 𝕜) :
    c • X = ⟨c • X.1, c * X.2⟩ := rfl

@[simp] private lemma add_fst (X Y : VirasoroAlgebra 𝕜) :
    (X + Y).1 = X.1 + Y.1 := rfl

@[simp] private lemma add_snd (X Y : VirasoroAlgebra 𝕜) :
    (X + Y).2 = X.2 + Y.2 := rfl

@[simp] private lemma smul_fst (c : 𝕜) (X : VirasoroAlgebra 𝕜) :
    (c • X).1 = c • X.1 := rfl

@[simp] private lemma smul_snd (c : 𝕜) (X : VirasoroAlgebra 𝕜) :
    (c • X).2 = c * X.2 := rfl

/-- The Virasoro algebra is a central extension of the Witt algebra. -/
instance isCentralExtension : LieAlgebra.IsCentralExtension (ofCentral 𝕜) toWittAlgebra :=
  LieTwoCocycle.CentralExtension.isCentralExtension _

/-- The (commonly used) `Lₙ` elements of the Virasoro algebra, for `n ∈ ℤ`. -/
noncomputable def lgen (n : ℤ) : VirasoroAlgebra 𝕜 :=
  ⟨WittAlgebra.lgen 𝕜 n, 0⟩

/-- The (commonly used) `C` central element of the Virasoro algebra. -/
noncomputable def cgen : VirasoroAlgebra 𝕜 := ofCentral 𝕜 1

lemma cgen_eq_ofCentral_one : cgen 𝕜 = ofCentral 𝕜 1 := rfl

private lemma cgen_eq' : cgen 𝕜 = ⟨0, 1⟩ := rfl

private lemma lgen_eq' (n : ℤ) : lgen 𝕜 n = ⟨WittAlgebra.lgen 𝕜 n, 0⟩ := rfl

lemma toWittAlgebra_cgen :
  toWittAlgebra (cgen 𝕜) = 0 := rfl

@[simp] lemma toWittAlgebra_lgen (n : ℤ) :
  toWittAlgebra (lgen 𝕜 n) = WittAlgebra.lgen 𝕜 n := rfl

@[simp] lemma cgen_bracket (Z : VirasoroAlgebra 𝕜) :
    ⁅cgen 𝕜, Z⁆ = 0 :=
  (isCentralExtension 𝕜).central 1 Z

@[simp] lemma lgen_bracket (n m : ℤ) :
    ⁅lgen 𝕜 n, lgen 𝕜 m⁆
      = (n - m : 𝕜) • lgen 𝕜 (n + m) + if n + m = 0 then ((n^3 - n : 𝕜)/12) • cgen 𝕜 else 0 := by
  simp_rw [bracket_def']
  by_cases h : n + m = 0
  · simp [h]
    apply ext'
    · simp [lgen, cgen_eq']
    · simp [WittAlgebra.virasoroCocycle_apply_lgen_lgen, lgen, cgen_eq', h]
  · simp [h]
    apply ext'
    · simp [lgen]
    · simp [WittAlgebra.virasoroCocycle_apply_lgen_lgen, h, lgen]

lemma lgen_bracket' (n m : ℤ) :
    ⁅lgen 𝕜 n, lgen 𝕜 m⁆
      = (n - m : 𝕜) • lgen 𝕜 (n + m) + if n + m = 0 then ((n-1 : 𝕜)*n*(n+1)/12) • cgen 𝕜 else 0 := by
  rw [lgen_bracket] ; congr ; ring

end VirasoroAlgebra -- namespace

end VirasoroAlgebra -- section

end VirasoroProject -- namespace
