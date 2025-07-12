import Mathlib
import VirasoroProject.LieAlgebraRepresentationOfBasis

namespace VirasoroProject



section auxiliary

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
def _root_.moduleOfModuleAlgebra (𝕜 A V : Type*) [CommRing 𝕜]
    [Semiring A] [Algebra 𝕜 A] [AddCommGroup V] [Module A V] :=
  V

instance (𝕜 A V : Type*) [CommRing 𝕜]
    [Semiring A] [Algebra 𝕜 A] [AddCommGroup V] [Module A V] :
    AddCommGroup (moduleOfModuleAlgebra 𝕜 A V) :=
  ‹AddCommGroup V›

instance (𝕜 A V : Type*) [CommRing 𝕜]
    [Semiring A] [Algebra 𝕜 A] [AddCommGroup V] [Module A V] :
    Module 𝕜 (moduleOfModuleAlgebra 𝕜 A V) :=
  moduleScalarOfModule 𝕜 A V

/-- The map from `V` to its type synonym `moduleOfModuleAlgebra 𝕜 A V`. -/
def _root_.moduleOfModuleAlgebra.mk (𝕜 A V : Type*) [CommRing 𝕜]
    [Semiring A] [Algebra 𝕜 A] [AddCommGroup V] [Module A V] (v : V) :
    moduleOfModuleAlgebra 𝕜 A V :=
  v

/-- The map from `V` to its type synonym `moduleOfModuleAlgebra 𝕜 A V` as a
homomorphism of additive groups. -/
def _root_.moduleOfModuleAlgebra.mkAddHom (𝕜 A V : Type*) [CommRing 𝕜]
    [Semiring A] [Algebra 𝕜 A] [AddCommGroup V] [Module A V] :
    V →+ moduleOfModuleAlgebra 𝕜 A V where
  toFun := moduleOfModuleAlgebra.mk 𝕜 A V
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The map from the type synonym `moduleOfModuleAlgebra 𝕜 A V` back to `V`. -/
def _root_.moduleOfModuleAlgebra.unMk (𝕜 A V : Type*) [CommRing 𝕜]
    [Semiring A] [Algebra 𝕜 A] [AddCommGroup V] [Module A V]
    (v : moduleOfModuleAlgebra 𝕜 A V) :
    V :=
  v

/-- The map from the type synonym `moduleOfModuleAlgebra 𝕜 A V` back to `V` as a
homomorphism of additive groups. -/
def _root_.moduleOfModuleAlgebra.unMkAddHom (𝕜 A V : Type*) [CommRing 𝕜]
    [Semiring A] [Algebra 𝕜 A] [AddCommGroup V] [Module A V] :
    moduleOfModuleAlgebra 𝕜 A V →+ V where
  toFun := moduleOfModuleAlgebra.unMk 𝕜 A V
  map_zero' := rfl
  map_add' _ _ := rfl

end auxiliary



section generalized_Verma_module

/-- The left ideal used in the construction of a (generalized) Verma module for an algebra `A`:
* `B ⊆ A` is a subset meant to act by scalar multiples on the highest weight vector
  (a "Borel subalgebra").
* `η : B → 𝕜` is a is a function giving those scalars ("highest weight" data). -/
def vermaIdeal {ι : Type*} {𝕜 A : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A]
    (η : ι → A × 𝕜) :
    Submodule A A :=
  Submodule.span A (Set.range <| fun (i : ι) ↦ (η i).1 - algebraMap 𝕜 A (η i).2)

/-- The (generalied) Verma module of an algebra `S` associated to a function `η : s → 𝕜`:
* `𝓝 ⊆ 𝓖` is a (nilpotent) Lie subalgebra meant to act as zero on the highest weight vector,
* `𝓗 ⊆ 𝓖` is a (commutative) Lie subalgebra (Cartan subalgebra) meant to act by scalar
  multiples determined by a functional `η : 𝓗 → 𝕜` on the highest weight vector. -/
def VermaModule {𝕜 A ι : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A]
    (η : ι → A × 𝕜) :=
  A ⧸ vermaIdeal η

/-- The highest weight vector in a (generalized) Verma module. -/
def VermaModule.hwVec {𝕜 A ι : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A] (η : ι → A × 𝕜) :
    VermaModule η :=
  Submodule.Quotient.mk 1

instance {𝕜 A ι : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A] (η : ι → A × 𝕜) :
    AddCommGroup (VermaModule η) :=
  Submodule.Quotient.addCommGroup _

instance {𝕜 A ι : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A] (η : ι → A × 𝕜) :
    Module A (VermaModule η) :=
  Submodule.Quotient.module _

lemma one_cyclic {R : Type*} [Semiring R] :
    Submodule.span R {(1 : R)} = ⊤ :=
  (Submodule.span_singleton_eq_top_iff R 1).mpr fun a ↦ ⟨a, by simp⟩

lemma LinearMap.apply_cyclic_of_cyclic_of_surjective {R : Type*} [Semiring R]
    {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
    {f : M₁ →ₗ[R] M₂} (f_surj : LinearMap.range f = ⊤)
    (m : M₁) (cyclic : Submodule.span R {m} = ⊤) :
    Submodule.span R {f m} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff] at *
  intro m₂
  obtain ⟨m₁, hm⟩ : ∃ m₁, f m₁ = m₂ := LinearMap.range_eq_top.mp f_surj m₂
  obtain ⟨a, ha⟩ := cyclic m₁
  refine ⟨a, by rw [← map_smul, ha, hm]⟩

/-- The highest weight vector in a Verma module is cyclic. -/
lemma VermaModule.hwVec_cyclic {𝕜 A ι : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A] (η : ι → A × 𝕜) :
    Submodule.span A {hwVec η} = ⊤ :=
  LinearMap.apply_cyclic_of_cyclic_of_surjective (Submodule.range_mkQ _) 1 one_cyclic

/-- The defining property of the highest weight vector in a Verma module. -/
lemma VermaModule.apply_hwVec_eq
    {𝕜 A ι : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A] (η : ι → A × 𝕜) (i : ι) :
    (η i).1 • hwVec η = (algebraMap 𝕜 A (η i).2) • hwVec η := by
  rw [show (algebraMap 𝕜 A (η i).2) • hwVec η
            = Submodule.Quotient.mk ((algebraMap 𝕜 A (η i).2) • 1) from rfl]
  rw [hwVec, ← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  apply (Submodule.Quotient.mk_eq_zero ..).mpr
  exact Submodule.mem_span_of_mem (by simp)

/-- A surjective module map from a ring to the submodule generated by a given vector. -/
def Ring.smulVectorₗ (A : Type*) [Ring A] {M : Type*} [AddCommGroup M] [Module A M] (m : M) :
    A →ₗ[A] M where
  toFun a := a • m
  map_add' a₁ a₂ := by simp [add_smul]
  map_smul' a₁ a₂ := by simp [mul_smul]

@[simp] lemma Ring.smulVectorₗ_one (A : Type*) [Ring A] {M : Type*} [AddCommGroup M] [Module A M]
    (m : M) :
    smulVectorₗ A m 1 = m := by
  simp [smulVectorₗ]

lemma Ring.range_smulVectorₗ_eq_span (A : Type*) [Ring A]
    {M : Type*} [AddCommGroup M] [Module A M] (m : M) :
    LinearMap.range (smulVectorₗ A m) = Submodule.span A {m} := by
  ext v
  rw [show v ∈ Submodule.span A {m} ↔ v ∈ (Submodule.span A {m} : Set M) from Eq.to_iff rfl]
  rw [Submodule.span_singleton_eq_range A m ]
  simp only [LinearMap.mem_range, Set.mem_range]
  rfl

lemma vermaIdeal_le_ker_smulVectorₗ {𝕜 A ι : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A]
    (η : ι → A × 𝕜) {M : Type*} [AddCommGroup M] [Module A M]
    {hwv : M} (hwv_prop : ∀ i, (η i).1 • hwv = algebraMap 𝕜 A (η i).2 • hwv) :
    vermaIdeal η ≤ LinearMap.ker (Ring.smulVectorₗ A hwv) := by
  simp only [vermaIdeal, Submodule.span_le]
  intro a ⟨i, a_eq⟩
  simp only [← a_eq, SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
  exact hwv_prop i

/-- The map guaranteed by the universal property of a Verma module. -/
def VermaModule.universalMap
    {𝕜 A ι : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A] (η : ι → A × 𝕜)
    {M : Type*} [AddCommGroup M] [Module A M]
    {hwv : M} (hwv_prop : ∀ i, (η i).1 • hwv = algebraMap 𝕜 A (η i).2 • hwv) :
    VermaModule η →ₗ[A] M :=
  Submodule.liftQ (vermaIdeal η) (Ring.smulVectorₗ A hwv) (vermaIdeal_le_ker_smulVectorₗ _ hwv_prop)

/-- The image of the highest weight vector of a Verma module under the map guaranteed by the
universal property is the assigned highest weight vector in the image module. -/
@[simp] lemma VermaModule.universalMap_hwVec
    {𝕜 A ι : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A] (η : ι → A × 𝕜)
    (M : Type*) [AddCommGroup M] [Module A M]
    (hwv : M) (hwv_prop : ∀ i, (η i).1 • hwv = algebraMap 𝕜 A (η i).2 • hwv) :
    universalMap η hwv_prop (hwVec η) = hwv := by
  convert Submodule.liftQ_apply (vermaIdeal η) (Ring.smulVectorₗ A hwv) 1
  simp

/-- The range of the map guaranteed by the universal property of a Verma module is the submodule
generated by the assigned highest weight vector in the image module. -/
lemma VermaModule.range_universalMap_eq_span
    {𝕜 A ι : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A] (η : ι → A × 𝕜)
    {M : Type*} [AddCommGroup M] [Module A M]
    {hwv : M} (hwv_prop : ∀ i, (η i).1 • hwv = algebraMap 𝕜 A (η i).2 • hwv) :
    LinearMap.range (universalMap η hwv_prop) = Submodule.span A {hwv} := by
  have key := VermaModule.hwVec_cyclic η ▸ Submodule.map_top (universalMap η hwv_prop)
  simp [← key, Submodule.map_span]

end generalized_Verma_module



section central_element_action

/-- In a module over a ring, left multiplication by a central element is a linear map. -/
def centralSMulHom {R : Type*} [Semiring R] {z : R} (z_central : ∀ a, z * a = a * z)
    (M : Type*) [AddCommMonoid M] [Module R M] :
    M →ₗ[R] M where
  toFun := Module.toAddMonoidEnd R M z
  map_add' := map_add ((Module.toAddMonoidEnd R M) z)
  map_smul' a v := by
    change z • a • v = a • z • v
    rw [← smul_assoc, ← mul_smul, ← z_central a, mul_smul, smul_assoc]

lemma centralSMulHom_apply {R : Type*} [Semiring R] {z : R} (z_central : ∀ a, Commute z a)
    (M : Type*) [AddCommMonoid M] [Module R M] (v : M) :
    centralSMulHom z_central M v = z • v :=
  rfl

variable {𝕜 A : Type*} [CommRing 𝕜] [Semiring A] [Algebra 𝕜 A]
variable (M : Type*) [AddCommGroup M] [Module 𝕜 M] [Module A M] [IsScalarTower 𝕜 A M]

/-- In a module over a ring, the set of vectors on which a given central element acts by
a given scalar multiple is a submodule. -/
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
  -- *A shorter (and in some sensemore elementary) proof:*
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



section

variable (𝕜 : Type*) [CommRing 𝕜]
variable (𝓖 : Type*) [LieRing 𝓖] [LieAlgebra 𝕜 𝓖]

@[inherit_doc UniversalEnvelopingAlgebra]
abbrev 𝓤 := UniversalEnvelopingAlgebra

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
    (hι : ∀ X, C (UniversalEnvelopingAlgebra.ι 𝕜 X))
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
    Commute (UniversalEnvelopingAlgebra.ι 𝕜 Z) a := by
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
    (hw : UniversalEnvelopingAlgebra.ι 𝕜 Z • w = algebraMap 𝕜 (𝓤 𝕜 𝓖) ζ • w) (v : V) :
    UniversalEnvelopingAlgebra.ι 𝕜 Z • v = algebraMap 𝕜 (𝓤 𝕜 𝓖) ζ • v := by
  have z_central (a : 𝓤 𝕜 𝓖) : Commute (UniversalEnvelopingAlgebra.ι 𝕜 Z) a :=
    UniversalEnvelopingAlgebra.central_of_forall_lie_eq_zero _ _ hZ _
  have ζ_central (a : 𝓤 𝕜 𝓖) : Commute (algebraMap 𝕜 _ ζ) a :=
    Algebra.commute_algebraMap_left ζ a
  let goodSubspace := LinearMap.ker (centralSMulHom z_central V - centralSMulHom ζ_central V)
  have good_iff (u : V) :
      u ∈ goodSubspace ↔ UniversalEnvelopingAlgebra.ι 𝕜 Z • u = algebraMap 𝕜 (𝓤 𝕜 𝓖) ζ • u := by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, goodSubspace]
    simpa only [centralSMulHom_apply] using sub_eq_zero
  rw [← good_iff]
  suffices ⊤ ≤ goodSubspace from this Submodule.mem_top
  rw [← w_cyclic]
  apply (Submodule.span_singleton_le_iff_mem ..).mpr
  exact (good_iff w).mpr hw

--variable {V : Type*} [AddCommGroup V] [Module (𝓤 𝕜 𝓖) V]
--#check @LieAlgebra.Representation 𝕜 𝕜 _ _ 𝓖 _ _ V _ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) _ _ _
--#check LinearMap.lsmul
--
--#check @Module.End 𝕜 V _ _ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V)
--#check @LinearMap.module 𝕜 𝕜 𝕜 V V _ _ _ _ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) (RingHom.id _) _ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) _
--#check @LinearMap 𝕜 𝕜 _ _ (RingHom.id _) V (@Module.End 𝕜 V _ _ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V)) _ _ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) (@LinearMap.module 𝕜 𝕜 𝕜 V V _ _ _ _ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) (RingHom.id _) _ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) _)

--variable (X : 𝓖)
--
--#check @Module.End 𝕜 V _ _ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) --_ _ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) (@LinearMap.module 𝕜 𝕜 𝕜 V V _ _ _ _ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V) -- (RingHom.id _) --_ (moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓖) V)
--
#check moduleOfModuleAlgebra.mkAddHom

private def UniversalEnvelopingAlgebra.representationAux
    (V : Type*) [AddCommGroup V] [Module (𝓤 𝕜 𝓖) V] (X : 𝓖) :
    -- V →ₗ[𝕜] V :=
    Module.End 𝕜 (moduleOfModuleAlgebra 𝕜 (𝓤 𝕜 𝓖) V) where
  toFun v :=
    (UniversalEnvelopingAlgebra.ι 𝕜 X) • (moduleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v)
  map_add' v₁ v₂ :=
    smul_add (UniversalEnvelopingAlgebra.ι 𝕜 X) (moduleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v₁) (moduleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v₂)
  map_smul' r v := by
    change
        (UniversalEnvelopingAlgebra.ι 𝕜 X) • (algebraMap 𝕜 (𝓤 𝕜 𝓖) r
              • (moduleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v))
          = algebraMap 𝕜 (𝓤 𝕜 𝓖) r • (UniversalEnvelopingAlgebra.ι 𝕜 X)
              • (moduleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v)
    simp only [← mul_smul]
    congr 1
    exact (Algebra.commutes r _).symm

private lemma UniversalEnvelopingAlgebra.representationAux_apply
    {V : Type*} [AddCommGroup V] [Module (𝓤 𝕜 𝓖) V] (X : 𝓖)
    (v : moduleOfModuleAlgebra 𝕜 (𝓤 𝕜 𝓖) V) :
    representationAux 𝕜 𝓖 V X v =
      (UniversalEnvelopingAlgebra.ι 𝕜 X)
        • (moduleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v) := by
  rfl

/-- Any module `V` over the universal enveloping algebra of a Lie algebra is a representation of the
Lie algebra.

This is recorded on the type synonym `moduleOfModuleAlgebra 𝕜 (𝓤 𝕜 𝓖) V` of `V`, in order to
make the `V` a `𝕜`-module and talk about a representation of a `𝕜`-Lie algebra on it. -/
def UniversalEnvelopingAlgebra.representation
    {V : Type*} [AddCommGroup V] [Module (𝓤 𝕜 𝓖) V] :
    LieAlgebra.Representation 𝕜 𝕜 𝓖 (moduleOfModuleAlgebra 𝕜 (𝓤 𝕜 𝓖) V) where
  toFun := representationAux 𝕜 𝓖 V
  map_add' X Y := by
    ext v
    simp only [LinearMap.add_apply, representationAux_apply, LieHom.map_add]
    exact Module.add_smul _ _ ((moduleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V) v)
  map_smul' r X := by
    ext v
    simp only [LinearMap.smul_apply, representationAux_apply]
    simp only [LieHom.map_smul, RingHom.id_apply]
    set v' := moduleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v with def_v'
    set a := (UniversalEnvelopingAlgebra.ι 𝕜 X) with def_a
    have : ((algebraMap 𝕜 (𝓤 𝕜 𝓖) r) • a) • v' = (algebraMap 𝕜 (𝓤 𝕜 𝓖) r) • a • v' :=
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
    set v' := moduleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 𝓖) V v with def_v'
    set a := (UniversalEnvelopingAlgebra.ι 𝕜 X) with def_a
    set b := (UniversalEnvelopingAlgebra.ι 𝕜 Y) with def_b
    change (a * b - b * a) • v' = a • (b • v') - b • (a • v')
    simp [sub_smul, mul_smul]

end

end VirasoroProject
