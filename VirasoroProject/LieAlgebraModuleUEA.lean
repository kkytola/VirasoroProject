/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import VirasoroProject.LieAlgebraRepresentationOfBasis
import Mathlib

/-!
# Modules over the universal enveloping algebra of a Lie algebra

...

## Main definitions

* ...

-/


section modules_over_algebras_are_modules_over_scalars

variable (𝕜 A : Type*) [CommRing 𝕜] [Semiring A] [Algebra 𝕜 A]

lemma Algebra.scalar_smul_eq_smul_algebraMap_mul (c : 𝕜) (a : A) :
    c • a = (c • (1 : A)) * a := by
  simp only [Algebra.smul_mul_assoc, one_mul]

lemma Algebra.smul_scalar_smul_eq_smul_algebraMap_mul (c : 𝕜) (a : A) :
    c • a = a * (c • (1 : A)) := by
  simp only [Algebra.mul_smul_comm, mul_one]

variable (V : Type*) [AddCommGroup V] [Module A V]

/-- Any module over an algebra is a module over the scalars. -/
def moduleScalarOfModule : Module 𝕜 V :=
  Module.compHom _ (algebraMap 𝕜 A)

lemma moduleScalarOfModule.smul_def (r : 𝕜) (v : V) :
    (moduleScalarOfModule 𝕜 A V).smul r v = algebraMap 𝕜 A r • v :=
  rfl

/-- When making any module over an algebra a module over the scalars, these form an
`IsScalarTower`.

(The reason this is needed as a separate lemma is that the actual meaning of the scalar
multiplication on representations of an algebra cannot be inferred by the type classes;
this must be hand-crafted by `moduleScalarOfModule` .) -/
lemma isScalarTowerModuleScalarOfModule :
    @IsScalarTower 𝕜 A V inferInstance inferInstance (moduleScalarOfModule 𝕜 A V).toSMul := by
  apply @IsScalarTower.mk ..
  intro c a v
  change (c • a) • v = algebraMap 𝕜 A c • a • v
  rw [Algebra.scalar_smul_eq_smul_algebraMap_mul]
  rw [mul_smul, Algebra.algebraMap_eq_smul_one c]

/-- Type synonym of a module over an algebra, when it is to be viewed as a module over
the scalars. -/
def _root_.ModuleOfModuleAlgebra (𝕜 A V : Type*) [CommRing 𝕜]
    [Semiring A] [Algebra 𝕜 A] [AddCommGroup V] [Module A V] :=
  V

instance : AddCommGroup (ModuleOfModuleAlgebra 𝕜 A V) :=
  ‹AddCommGroup V›

instance : Module 𝕜 (ModuleOfModuleAlgebra 𝕜 A V) :=
  moduleScalarOfModule 𝕜 A V

/-- The map from `V` to its type synonym `ModuleOfModuleAlgebra 𝕜 A V`. -/
def _root_.ModuleOfModuleAlgebra.mk (v : V) :
    ModuleOfModuleAlgebra 𝕜 A V :=
  v

/-- The map from `V` to its type synonym `ModuleOfModuleAlgebra 𝕜 A V` as a
homomorphism of additive groups. -/
def _root_.ModuleOfModuleAlgebra.mkAddHom :
    V →+ ModuleOfModuleAlgebra 𝕜 A V where
  toFun := ModuleOfModuleAlgebra.mk 𝕜 A V
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The map from the type synonym `ModuleOfModuleAlgebra 𝕜 A V` back to `V`. -/
def _root_.ModuleOfModuleAlgebra.unMk (v : ModuleOfModuleAlgebra 𝕜 A V) :
    V :=
  v

/-- The map from the type synonym `ModuleOfModuleAlgebra 𝕜 A V` back to `V` as a
homomorphism of additive groups. -/
def _root_.ModuleOfModuleAlgebra.unMkAddHom (𝕜 A V : Type*) [CommRing 𝕜]
    [Semiring A] [Algebra 𝕜 A] [AddCommGroup V] [Module A V] :
    ModuleOfModuleAlgebra 𝕜 A V →+ V where
  toFun := ModuleOfModuleAlgebra.unMk 𝕜 A V
  map_zero' := rfl
  map_add' _ _ := rfl

end modules_over_algebras_are_modules_over_scalars



section left_smul_linear_map

variable (𝕜 : Type*) [CommRing 𝕜]
variable {A : Type*} [Semiring A] [Algebra 𝕜 A]
variable (V : Type*) [AddCommGroup V] [Module A V]

def ModuleOfModuleAlgebra.lsmul (a : A) :
    ModuleOfModuleAlgebra 𝕜 A V →ₗ[𝕜] ModuleOfModuleAlgebra 𝕜 A V where
  toFun v := ModuleOfModuleAlgebra.mkAddHom 𝕜 A V (a • ModuleOfModuleAlgebra.unMkAddHom 𝕜 A V v)
  map_add' v₁ v₂ :=
    smul_add a (ModuleOfModuleAlgebra.unMkAddHom 𝕜 A V v₁) (ModuleOfModuleAlgebra.unMkAddHom 𝕜 A V v₂)
  map_smul' r v := by
    change a • (algebraMap 𝕜 A r • (ModuleOfModuleAlgebra.unMkAddHom 𝕜 A V v))
          = algebraMap 𝕜 A r • (a • (ModuleOfModuleAlgebra.unMkAddHom 𝕜 A V v))
    simp [← smul_assoc]
    congr 1
    exact (Algebra.commutes r a).symm

lemma ModuleOfModuleAlgebra.lsmul_apply (a : A) (v : ModuleOfModuleAlgebra 𝕜 A V) :
    ModuleOfModuleAlgebra.lsmul 𝕜 V a v =
      ModuleOfModuleAlgebra.mkAddHom 𝕜 A V (a • ModuleOfModuleAlgebra.unMkAddHom 𝕜 A V v) := by
  rfl

end left_smul_linear_map



section central_element_action

variable {R : Type*} [Semiring R]

/-- In a module over a ring, left multiplication by a central element is a linear map. -/
def centralSMulHom {z : R} (z_central : ∀ a, z * a = a * z)
    (M : Type*) [AddCommMonoid M] [Module R M] :
    M →ₗ[R] M where
  toFun := Module.toAddMonoidEnd R M z
  map_add' := map_add ((Module.toAddMonoidEnd R M) z)
  map_smul' a v := by
    change z • a • v = a • z • v
    rw [← smul_assoc, ← mul_smul, ← z_central a, mul_smul, smul_assoc]

lemma centralSMulHom_apply {z : R} (z_central : ∀ a, Commute z a)
    (M : Type*) [AddCommMonoid M] [Module R M] (v : M) :
    centralSMulHom z_central M v = z • v :=
  rfl

variable {𝕜 A : Type*} [CommRing 𝕜] [Semiring A] [Algebra 𝕜 A]
variable (M : Type*) [AddCommGroup M] [Module 𝕜 M] [Module A M] [IsScalarTower 𝕜 A M]

/-- The set of vectors on which a given central element acts by a given scalar multiple as
a submodule. -/
def centralValueSubmodule {z : A} (z_central : ∀ a, Commute z a) (ζ : 𝕜) :
    Submodule A M :=
  LinearMap.ker (centralSMulHom z_central M - ζ • (LinearMap.id ..))

/-- The defining property of `centralValueSubmodule` is the eigenvalue property for the central
element action. -/
lemma mem_centralValueSubmodule_iff {z : A} (z_central : ∀ a, Commute z a) (ζ : 𝕜) (v : M) :
    v ∈ centralValueSubmodule M z_central ζ ↔ z • v = ζ • v := by
  simp only [centralValueSubmodule, LinearMap.mem_ker, LinearMap.sub_apply, centralSMulHom_apply,
             LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  grind

lemma smul_eq_scalar_smul_of_central_of_mem_span
    {z : A} (z_central : ∀ a, Commute z a) {u : M} {ζ : 𝕜}
    (hzu : z • u = ζ • u) {v : M} (hv : v ∈ Submodule.span A {u}) :
    z • v = ζ • v := by
  rw [← mem_centralValueSubmodule_iff]
  suffices Submodule.span A {u} ≤ centralValueSubmodule M z_central ζ from this hv
  apply (Submodule.span_singleton_le_iff_mem u _).mpr
  exact (mem_centralValueSubmodule_iff ..).mpr hzu
  -- *A shorter (and in some sense more elementary) proof:*
  --obtain ⟨a, hauv⟩ := Submodule.mem_span_singleton.mp hv
  --rw [← hauv, ← smul_assoc, smul_eq_mul, z_central a, ← smul_eq_mul, smul_assoc, hau]
  --exact smul_comm a ζ u

lemma smul_eq_scalar_smul_of_central
    {z : A} (z_central : ∀ a, Commute z a) {u : M} {ζ : 𝕜}
    (hau : z • u = ζ • u) {v : M} (v_cyclic : Submodule.span A {u} = ⊤) :
    z • v = ζ • v := by
  apply smul_eq_scalar_smul_of_central_of_mem_span _ z_central hau
  simp [v_cyclic]

end central_element_action



section UniversalEnvelopingAlgebra

variable (𝕜 : Type*) [CommRing 𝕜]
variable (𝓖 : Type*) [LieRing 𝓖] [LieAlgebra 𝕜 𝓖]

@[inherit_doc UniversalEnvelopingAlgebra]
abbrev 𝓤 := UniversalEnvelopingAlgebra

@[inherit_doc UniversalEnvelopingAlgebra.ι]
abbrev ιUEA := UniversalEnvelopingAlgebra.ι

-- TODO: To Mathlib...
lemma UniversalEnvelopingAlgebra.mkAlgHom_range_eq_top :
    (UniversalEnvelopingAlgebra.mkAlgHom 𝕜 𝓖).range = ⊤ := by
  simp only [UniversalEnvelopingAlgebra.mkAlgHom, RingQuot.mkAlgHom]
  rw [AlgHom.range_eq_top]
  exact RingQuot.mkRingHom_surjective (UniversalEnvelopingAlgebra.Rel 𝕜 𝓖)

variable {𝕜 𝓖} in
lemma UniversalEnvelopingAlgebra.mkAlgHom_surjective :
    Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom 𝕜 𝓖) := by
  simpa [← AlgHom.range_eq_top] using mkAlgHom_range_eq_top 𝕜 𝓖

-- TODO: To Mathlib...
lemma UniversalEnvelopingAlgebra.induction
    (C : 𝓤 𝕜 𝓖 → Prop) (hAM : ∀ r, C (algebraMap 𝕜 (𝓤 𝕜 𝓖) r))
    (hι : ∀ X, C (ιUEA 𝕜 X))
    (hMul : ∀ a b, C a → C b → C (a * b)) (hAdd : ∀ a b, C a → C b → C (a + b)) (a : 𝓤 𝕜 𝓖) :
    C a := by
  let C' : TensorAlgebra 𝕜 𝓖 → Prop := fun t ↦ C (UniversalEnvelopingAlgebra.mkAlgHom _ _ t)
  suffices ∀ t, C' t by
    obtain ⟨t, ht⟩ := UniversalEnvelopingAlgebra.mkAlgHom_surjective a
    simpa only [← ht] using this t
  apply TensorAlgebra.induction (C := C')
  · intro r
    simpa [C'] using hAM r
  · intro X
    exact hι X
  · intro ta tb hta htb
    simpa only [C', map_mul] using hMul _ _ hta htb
  · intro ta tb hta htb
    simpa only [C', map_add] using hAdd _ _ hta htb

lemma UniversalEnvelopingAlgebra.central_of_forall_lie_eq_zero
    {Z : 𝓖} (hZ : ∀ (X : 𝓖), ⁅Z, X⁆ = 0) (a : 𝓤 𝕜 𝓖) :
    Commute (ιUEA 𝕜 Z) a := by
  apply UniversalEnvelopingAlgebra.induction 𝕜 𝓖
        (fun b ↦ Commute (UniversalEnvelopingAlgebra.ι 𝕜 Z) b)
  · intro r
    exact Algebra.commute_algebraMap_right r ((UniversalEnvelopingAlgebra.ι 𝕜) Z)
  · intro X
    apply commute_iff_lie_eq.mpr
    rw [← LieHom.map_lie, hZ X, LieHom.map_zero]
  · intro a b ha hb
    exact Commute.mul_right ha hb
  · intro a b ha hb
    exact Commute.add_right ha hb

/-- If a central element of a Lie algebra acts as a scalar multiplication on a cyclic
vector in a representation, then it acts as the same scalar on the whole representation. -/
lemma UniversalEnvelopingAlgebra.smul_eq_of_cyclic_of_forall_lie_eq_zero
    {Z : 𝓖} {ζ : 𝕜} (hZ : ∀ (X : 𝓖), ⁅Z, X⁆ = 0)
    {V : Type*} [AddCommGroup V] [Module (𝓤 𝕜 𝓖) V]
    {w : V} (w_cyclic : Submodule.span (𝓤 𝕜 𝓖) {w} = ⊤)
    (hw : ιUEA 𝕜 Z • w = algebraMap 𝕜 (𝓤 𝕜 𝓖) ζ • w) (v : V) :
    ιUEA 𝕜 Z • v = algebraMap 𝕜 (𝓤 𝕜 𝓖) ζ • v := by
  have z_central (a : 𝓤 𝕜 𝓖) : Commute (ιUEA 𝕜 Z) a :=
    UniversalEnvelopingAlgebra.central_of_forall_lie_eq_zero _ _ hZ _
  have ζ_central (a : 𝓤 𝕜 𝓖) : Commute (algebraMap 𝕜 _ ζ) a :=
    Algebra.commute_algebraMap_left ζ a
  let goodSubspace := LinearMap.ker (centralSMulHom z_central V - centralSMulHom ζ_central V)
  have good_iff (u : V) :
      u ∈ goodSubspace ↔ ιUEA 𝕜 Z • u = algebraMap 𝕜 (𝓤 𝕜 𝓖) ζ • u := by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, goodSubspace]
    simpa only [centralSMulHom_apply] using sub_eq_zero
  rw [← good_iff]
  suffices ⊤ ≤ goodSubspace from this Submodule.mem_top
  rw [← w_cyclic]
  apply (Submodule.span_singleton_le_iff_mem ..).mpr
  exact (good_iff w).mpr hw

/-- Auxiliary `𝕜`-linear map `V →ₗ[𝕜] V` defined by left multiplication by `X : 𝓖` in a module
over `𝓤 𝕜 𝓖`. -/
private def UniversalEnvelopingAlgebra.representationAux
    (V : Type*) [AddCommGroup V] [Module (𝓤 𝕜 𝓖) V] (X : 𝓖) :
    Module.End 𝕜 (ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 𝓖) V) where
  toFun v :=
    (ιUEA 𝕜 X) • (ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v)
  map_add' v₁ v₂ :=
    smul_add (ιUEA 𝕜 X) (ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v₁)
                        (ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v₂)
  map_smul' r v := by
    change
        (ιUEA 𝕜 X) • (algebraMap 𝕜 (𝓤 𝕜 𝓖) r
              • (ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v))
          = algebraMap 𝕜 (𝓤 𝕜 𝓖) r • (ιUEA 𝕜 X)
              • (ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v)
    simp only [← mul_smul]
    congr 1
    exact (Algebra.commutes r _).symm

private lemma UniversalEnvelopingAlgebra.representationAux_apply
    {V : Type*} [AddCommGroup V] [Module (𝓤 𝕜 𝓖) V] (X : 𝓖)
    (v : ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 𝓖) V) :
    representationAux 𝕜 𝓖 V X v =
      (ιUEA 𝕜 X) • (ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v) := by
  rfl

/-- Any module `V` over the universal enveloping algebra of a Lie algebra is a representation of the
Lie algebra.

This is recorded on the type synonym `ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 𝓖) V` of `V`, in order to
make the `V` a `𝕜`-module and talk about a representation of a `𝕜`-Lie algebra on it. -/
def UniversalEnvelopingAlgebra.representation
    {V : Type*} [AddCommGroup V] [Module (𝓤 𝕜 𝓖) V] :
    LieAlgebra.Representation 𝕜 𝕜 𝓖 (ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 𝓖) V) where
  toFun := representationAux 𝕜 𝓖 V
  map_add' X Y := by
    ext v
    simp only [LinearMap.add_apply, representationAux_apply, LieHom.map_add]
    exact Module.add_smul _ _ ((ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V) v)
  map_smul' r X := by
    ext v
    simp only [LinearMap.smul_apply, representationAux_apply]
    simp only [LieHom.map_smul, RingHom.id_apply]
    set v' := ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v with def_v'
    set a := ιUEA 𝕜 X with def_a
    have : ((algebraMap 𝕜 (𝓤 𝕜 𝓖) r) • a) • v' = algebraMap 𝕜 (𝓤 𝕜 𝓖) r • a • v' :=
      IsScalarTower.smul_assoc ((algebraMap 𝕜 (𝓤 𝕜 𝓖)) r) a v'
    convert this using 1
    congr 1
    exact algebra_compatible_smul (𝓤 𝕜 𝓖) r a
  map_lie' := by
    intro X Y
    ext v
    change (representationAux 𝕜 𝓖 V ⁅X, Y⁆) v
          = representationAux 𝕜 𝓖 V X (representationAux 𝕜 𝓖 V Y v)
            - representationAux 𝕜 𝓖 V Y (representationAux 𝕜 𝓖 V X v)
    simp only [representationAux_apply, LieHom.map_lie]
    set v' := ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v with def_v'
    set a := (ιUEA 𝕜 X) with def_a
    set b := (ιUEA 𝕜 Y) with def_b
    change (a * b - b * a) • v' = a • (b • v') - b • (a • v')
    simp [sub_smul, mul_smul]

section moduleUEA

variable {𝕜 𝕂 : Type*} [CommRing 𝕜] [CommRing 𝕂]
variable  {𝓖 : Type*} [LieRing 𝓖] [LieAlgebra 𝕜 𝓖]
variable {V : Type*} [AddCommGroup V] [Module 𝕂 V] [Module 𝕜 V]
variable [SMul 𝕜 𝕂] [IsScalarTower 𝕜 𝕂 V] [SMulCommClass 𝕂 𝕜 V]
variable (ρ : LieAlgebra.Representation 𝕜 𝕂 𝓖 V)

/-- A representation of a `𝕜`-Lie algebra `𝓖` on a vector space `V` defines a `𝓤 𝕜 𝓖`-module
structure on `V`. -/
noncomputable def LieAlgebra.Representation.moduleUniversalEnvelopingAlgebra :
    Module (𝓤 𝕜 𝓖) V where
  smul a v := UniversalEnvelopingAlgebra.lift 𝕜 ρ a v
  one_smul v := by
    change UniversalEnvelopingAlgebra.lift 𝕜 ρ (1 : 𝓤 𝕜 𝓖) v = v
    simp
  mul_smul a b v := by
    change UniversalEnvelopingAlgebra.lift 𝕜 ρ (a * b) v
            = UniversalEnvelopingAlgebra.lift 𝕜 ρ a (UniversalEnvelopingAlgebra.lift 𝕜 ρ b v)
    simp
  smul_zero a := by
    change UniversalEnvelopingAlgebra.lift 𝕜 ρ a 0 = 0
    simp
  smul_add a v₁ v₂ := by
    change UniversalEnvelopingAlgebra.lift 𝕜 ρ a (v₁ + v₂)
            = UniversalEnvelopingAlgebra.lift 𝕜 ρ a v₁ + UniversalEnvelopingAlgebra.lift 𝕜 ρ a v₂
    simp
  add_smul a₁ a₂ v := by
    change UniversalEnvelopingAlgebra.lift 𝕜 ρ (a₁ + a₂) v
            = UniversalEnvelopingAlgebra.lift 𝕜 ρ a₁ v + UniversalEnvelopingAlgebra.lift 𝕜 ρ a₂ v
    simp
  zero_smul v := by
    change UniversalEnvelopingAlgebra.lift 𝕜 ρ 0 v = 0
    simp

@[simp] lemma LieAlgebra.Representation.moduleUniversalEnvelopingAlgebra_smul_eq
    (a : 𝓤 𝕜 𝓖) (v : V) :
    (LieAlgebra.Representation.moduleUniversalEnvelopingAlgebra ρ).smul a v
      = UniversalEnvelopingAlgebra.lift 𝕜 ρ a v :=
  rfl

/-- The defining property of the `𝓤 𝕜 𝓖`-module structure on a representation `V` of a
`𝕜`-Lie algebra `𝓖`. -/
lemma LieAlgebra.Representation.moduleUniversalEnvelopingAlgebra_ιUEA_smul_eq
    (X : 𝓖) (v : V) :
    (LieAlgebra.Representation.moduleUniversalEnvelopingAlgebra ρ).smul (ιUEA 𝕜 X) v = ρ X v := by
  simp only [UniversalEnvelopingAlgebra.ι_apply, moduleUniversalEnvelopingAlgebra_smul_eq,
             UniversalEnvelopingAlgebra.lift_ι_apply']

end moduleUEA

end UniversalEnvelopingAlgebra
