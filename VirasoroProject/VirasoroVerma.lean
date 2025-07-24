/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib
import VirasoroProject.VermaModule
import VirasoroProject.VirasoroAlgebra



namespace VirasoroProject



section

variable (𝕜 : Type*) [CommRing 𝕜]
variable (𝓰 : Type*) [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]

structure TriangularDecomposition where
  --subalg : SignType → LieSubalgebra 𝕜 𝓰
  --directSum : DirectSum.IsInternal subalg
  --commutative : ∀ (H₁ H₂ : subalg 0), ⁅H₁, H₂⁆ = 0
  --nilpotent : ...
  part : SignType → Submodule 𝕜 𝓰
  directSum : DirectSum.IsInternal part

namespace TriangularDecomposition

-- TODO: To Mathlib...
lemma finsum_mem_span {ι R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) :
    ∑ᶠ i, cfs i • vs i ∈ Submodule.span R (Set.range vs) := by
  by_cases h : {i | cfs i • vs i ≠ 0}.Finite
  · let s : Finset ι := h.toFinset
    rw [finsum_eq_finset_sum_of_support_subset (s := s) _ (fun i hi ↦ by simpa [s] using hi)]
    apply Submodule.sum_smul_mem
    exact fun i his ↦ Submodule.mem_span_of_mem (Set.mem_range_self i)
  · suffices junk : ∑ᶠ i, cfs i • vs i = 0 by simp [junk]
    simpa using finsum_mem_eq_zero_of_infinite (s := Set.univ) (by simpa using h)

-- TODO: To Mathlib... (Golf first, though...)
lemma finsum_mem_mem_span {ι R V : Type*}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) (s : Set ι) :
    ∑ᶠ i ∈ s, cfs i • vs i ∈ Submodule.span R (vs '' s) := by
  by_cases h : {i | cfs i • vs i ≠ 0 ∧ i ∈ s}.Finite
  · let t : Finset ι := h.toFinset
    rw [finsum_eq_finset_sum_of_support_subset (s := t) _ ?_]
    · classical
      have aux : ∑ i ∈ t, ∑ᶠ (_ : i ∈ s), cfs i • vs i = ∑ i ∈ t.filter s, cfs i • vs i  := by
        rw [Finset.sum_filter]
        congr 1
        funext i
        by_cases his : i ∈ s <;>
        · simpa [his] using fun con ↦ by contradiction
      rw [aux]
      apply Submodule.sum_smul_mem
      intro i hist
      apply Submodule.mem_span_of_mem <| Set.mem_image_of_mem ..
      simp_all only [ne_eq, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, t]
    · intro i hi
      simp only [ne_eq, Set.Finite.coe_toFinset, Set.mem_setOf_eq, t]
      refine ⟨?_, ?_⟩ <;>
      · by_contra con
        simp [con] at hi
  · suffices junk : ∑ᶠ i ∈ s, cfs i • vs i = 0 by simp [junk]
    exact finsum_mem_eq_zero_of_infinite (by simpa [and_comm] using h)

-- TODO: To Mathlib.
lemma _root_.Basis.finsum_repr_smul_basis {R M ι : Type*} [Semiring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] (B : Basis ι R M) (v : M) :
    ∑ᶠ i, B.repr v i • B i = v := by
  have obs : (Function.support fun i ↦ B.repr v i • B i).Finite := by
    apply (Finsupp.finite_support (B.repr v)).subset
    intro i hi
    simp only [Function.support, ne_eq, smul_eq_zero, not_or, Set.mem_setOf_eq] at hi ⊢
    exact hi.1
  rw [finsum_eq_sum _ obs]
  apply B.repr.injective
  rw [map_sum]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
  ext i
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ j_ne_i
    simp [j_ne_i]
  · simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, smul_eq_zero, not_or, not_and,
               not_not, Finsupp.single_eq_same]
    intro hi
    rw [← not_imp_not, not_not] at hi
    exact hi (B.ne_zero i)

-- TODO: To Mathlib.
lemma _root_.Basis.repr_finsum {R M ι : Type*} [Semiring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] (B : Basis ι R M) (cf : ι →₀ R) :
    B.repr (∑ᶠ i, cf i • B i) = cf := by
  convert show B.repr (B.repr.symm cf) = cf by simp
  have aux_finite : (Function.support fun i ↦ cf i • B i).Finite := by
    apply (Finsupp.finite_support cf).subset
    intro i hi
    simp only [Function.support, ne_eq, smul_eq_zero, not_or, Set.mem_setOf_eq] at hi ⊢
    exact hi.1
  rw [finsum_eq_sum _ aux_finite]
  simp only [Basis.repr_symm_apply, Finsupp.linearCombination, Finsupp.coe_lsum,
             LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Finsupp.sum]
  congr
  ext i
  simp [Basis.ne_zero B i]

-- TODO: To Mathlib.
lemma _root_.Basis.repr_finsum_mem_eq_ite {R M ι : Type*} [Semiring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] (B : Basis ι R M) (cf : ι →₀ R)
    (I : Set ι) [DecidablePred fun i ↦ i ∈ I] (j : ι) :
    B.repr (∑ᶠ i ∈ I, cf i • B i) j = if j ∈ I then cf j else 0 := by
  let cf'' := I.indicator cf
  let cf' : ι →₀ R := {
    support := (cf.support.finite_toSet.inter_of_left I).toFinset
    toFun := I.indicator cf
    mem_support_toFun i := by simp [and_comm]
  }
  have key := B.repr_finsum cf'
  simp only [Finsupp.ext_iff] at key
  have aux (i : ι) : cf' i = if i ∈ I then cf i else 0 := by simp [cf', Set.indicator]
  rw [← aux j, ← key j]
  congr
  ext i
  by_cases hi : i ∈ I <;> simp [hi, aux i]

-- TODO: To Mathlib.
lemma _root_.Basis.iSupIndep_submodule_span_of_pairwise_disjoint
    {R M ι κ : Type*} [Semiring R] [AddCommGroup M] [Module R M]
    (B : Basis ι R M) (Is : κ → Set ι)
    (Is_disj : Pairwise (fun k₁ k₂ ↦ Disjoint (Is k₁) (Is k₂))) :
    iSupIndep fun k ↦ Submodule.span R (B '' (Is k)) := by
  intro k
  simp only [Disjoint, ne_eq, le_bot_iff, Submodule.eq_bot_iff]
  intro U hUk hU v hv
  have hvk := hUk hv
  have hv' := hU hv
  simp only [Submodule.iSup_span, ← Set.image_iUnion] at hv'
  rw [Basis.mem_span_image] at hvk hv'
  suffices B.repr v = 0 by simpa using this
  suffices (B.repr v).support = ∅ by simpa using this
  apply Finset.eq_empty_of_forall_notMem
  exact iSupIndep_iff_pairwiseDisjoint.mpr Is_disj k hvk hv'

variable {𝕜 𝓰} in
def ofBasis {ι : Type*} [Nontrivial 𝕜] [NoZeroSMulDivisors 𝕜 𝓰]
    (B : Basis ι 𝕜 𝓰) (Bp : SignType → Set ι)
    (Bp_disj : Pairwise (fun ε₁ ε₂ ↦ Disjoint (Bp ε₁) (Bp ε₂)))
    (Bp_cover : ⋃ ε, Bp ε = Set.univ) :
    TriangularDecomposition 𝕜 𝓰 where
  part ε := Submodule.span 𝕜 (B '' Bp ε)
    --Submodule.span 𝕜 (Set.range fun (j : Bp ε) ↦ B j)
  directSum := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · exact B.iSupIndep_submodule_span_of_pairwise_disjoint _ Bp_disj
    · rw [Submodule.eq_top_iff']
      intro X
      have Xpart_mem (ε) : ∑ᶠ i ∈ Bp ε, B.repr X i • B i ∈ Submodule.span 𝕜 (B '' Bp ε) :=
        finsum_mem_mem_span (fun i ↦ B i) (B.repr X) (Bp ε)
      have X_eq :
          X = ∑ᶠ i ∈ Bp 1, B.repr X i • B i + ∑ᶠ i ∈ Bp (-1), B.repr X i • B i
              + ∑ᶠ i ∈ Bp 0, B.repr X i • B i := by
        nth_rw 1 [← B.finsum_repr_smul_basis X]
        have supp_finite_aux : (Function.support (fun i ↦ B.repr X i • B i)).Finite := by
          apply (Finsupp.finite_support (B.repr X)).subset
          intro i hi
          simp only [Function.support, ne_eq, smul_eq_zero, not_or, Set.mem_setOf_eq] at hi ⊢
          exact hi.1
        have supp_finite (ε : SignType) := supp_finite_aux.inter_of_right (Bp ε)
        rw [← finsum_mem_union' (Bp_disj (by simp)) (supp_finite 1) (supp_finite (-1))]
        rw [← finsum_mem_union' ?_ ?_ (supp_finite 0)]
        · have Bp_cover' : Bp 1 ∪ Bp (-1) ∪ Bp 0 = Set.univ := by
            rw [← Bp_cover]
            apply subset_antisymm
            · refine Set.union_subset (Set.union_subset ?_ ?_) ?_ <;>
              · exact Set.subset_iUnion_of_subset _ subset_rfl
            · apply Set.iUnion_subset
              intro ε
              match ε with
              | 1 => apply Set.subset_union_of_subset_left (by simp)
              | 0 => simp
              | -1 => apply Set.subset_union_of_subset_left (by simp)
          simp [Bp_cover']
        · exact Disjoint.union_left (Bp_disj (by simp)) (Bp_disj (by simp))
        · exact Set.Finite.inter_of_right supp_finite_aux (Bp 1 ∪ Bp (-1))
      rw [X_eq]
      apply Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
      · exact Submodule.mem_iSup_of_mem 0 (Xpart_mem 0)
      · exact Submodule.mem_iSup_of_mem 1 (Xpart_mem 1)
      · exact Submodule.mem_iSup_of_mem (-1) (Xpart_mem (-1))

lemma smul_support_subset_left {R M ι : Type*} [Semiring R]
    [AddCommGroup M] [Module R M] (v : ι → M) (cf : ι → R) :
    (fun i ↦ cf i • v i).support ⊆ cf.support := by
  simp only [Function.support_subset_iff, ne_eq, Function.mem_support]
  intro i
  rw [not_imp_not]
  intro hcf
  simp [hcf]

-- TODO: To Mathlib?
-- The closest I found: `Basis.ofSpan_subset`, `Basis.ofSpan`, `Basis.flag`
noncomputable def _root_.Basis.basis_submodule_span {R M ι : Type*} [Semiring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] (B : Basis ι R M) (I : Set ι) :
    Basis I R (Submodule.span R (B '' I)) :=
  let f : Submodule.span R (B '' I) →ₗ[R] (I →₀ R) := {
    toFun v := Finsupp.subtypeDomain (fun x ↦ x ∈ I) (B.repr v)
    map_add' v₁ v₂ := by simp
    map_smul' r v := by
      simp only [SetLike.val_smul, map_smul, RingHom.id_apply]
      exact Finsupp.ext (congrFun rfl) }
  let g : (I →₀ R) →ₗ[R] Submodule.span R (B '' I) := {
    toFun cf := ⟨∑ᶠ i, cf i • B i, by convert finsum_mem_span (fun (i : I) ↦ B i) cf ; aesop⟩
    map_add' cf₁ cf₂ := by
      simp only [Finsupp.coe_add, Pi.add_apply, AddMemClass.mk_add_mk, Subtype.mk.injEq]
      rw [← finsum_add_distrib]
      · simp [add_smul]
      · exact cf₁.finite_support.subset <| smul_support_subset_left ..
      · exact cf₂.finite_support.subset <| smul_support_subset_left ..
    map_smul' r cf := by
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_assoc, RingHom.id_apply, SetLike.mk_smul_mk,
                 smul_finsum] }
  --have f_injective : Function.Injective f := by
  --  rw [Setoid.injective_iff_ker_bot]
  --  ext u₁ u₂
  --  simp only [Setoid.ker, LinearMap.coe_mk, AddHom.coe_mk, Function.onFun, Setoid.bot_def, f]
  --  constructor
  --  · intro h
  --    suffices B.repr u₁ = B.repr u₂ by simpa using this
  --    ext i
  --    by_cases hiI : i ∈ I
  --    · simp only [Finsupp.subtypeDomain, Finsupp.mk.injEq] at h
  --      exact congr_fun h.2 ⟨i, hiI⟩
  --    · have hu₁ := (B.mem_span_image (s := I)).mp (Submodule.coe_mem u₁)
  --      have hu₂ := (B.mem_span_image (s := I)).mp (Submodule.coe_mem u₂)
  --      simp only [Finsupp.support_subset_iff] at hu₁ hu₂
  --      simp [hu₁ _ hiI, hu₂ _ hiI]
  --  · intro hu
  --    simp [hu]
  --have f_surjective : Function.Surjective f := by
  --  intro cf
  --  use ⟨∑ᶠ i, cf i • B i, by convert finsum_mem_span (fun (i : I) ↦ B i) cf ; aesop⟩
  --  ext i
  --  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.subtypeDomain_apply]
  --  classical
  --  have aux := B.repr_finsum_mem_eq_ite cf.extendDomain I i
  --  simp only [Finsupp.extendDomain_toFun, dite_smul, zero_smul, Subtype.coe_prop, ↓reduceIte,
  --             ↓reduceDIte, Subtype.coe_eta] at aux
  --  simp [← aux, ← finsum_set_coe_eq_finsum_mem]
  --⟨LinearEquiv.ofBijective f ⟨f_injective, f_surjective⟩⟩
  have fog : f ∘ g = id := by
    funext cf
    ext i
    simp only [f, g, LinearMap.coe_mk, AddHom.coe_mk]
    classical
    have aux := B.repr_finsum_mem_eq_ite cf.extendDomain I i
    simp only [Finsupp.extendDomain_toFun, dite_smul, zero_smul, Subtype.coe_prop, ↓reduceIte,
               ↓reduceDIte, Subtype.coe_eta] at aux
    simp [← aux, ← finsum_set_coe_eq_finsum_mem]
  have gof : g ∘ f = id := by
    funext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Finsupp.subtypeDomain_apply,
               id_eq, g, f]
    ext
    dsimp
    nth_rw 2 [← B.finsum_repr_smul_basis v]
    rw [@finsum_set_coe_eq_finsum_mem ι M _ (fun i ↦ (B.repr v) i • B i) I]
    congr 1
    ext j
    by_cases hj : j ∈ I
    · simp [hj]
    · simp only [hj, finsum_false]
      simp [show B.repr v j = 0
            from Finsupp.notMem_support_iff.mp fun h ↦
              hj ((Basis.mem_span_image ..).mp (Submodule.coe_mem v) h)]
  ⟨{
    toFun := f
    map_add' x y := LinearMap.map_add f x y
    map_smul' m x := LinearMap.CompatibleSMul.map_smul f m x
    invFun := g
    left_inv := by exact congrFun gof
    right_inv := by exact congrFun fog
  }⟩
  --⟨LinearEquiv.ofBijective f ⟨f_injective, f_surjective⟩⟩

-- TODO: To Mathlib?
@[simp] lemma _root_.Basis.basis_submodule_span_apply {R M ι : Type*}
    [Semiring R] [Nontrivial R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
    (B : Basis ι R M) (I : Set ι) (i : I) :
    B.basis_submodule_span I i = B i.val := by
  simp only [Basis.basis_submodule_span, LinearMap.coe_mk, AddHom.coe_mk, Basis.coe_ofRepr,
             LinearEquiv.coe_symm_mk]
  rw [finsum_eq_single _ i]
  · simp
  · intro j hj
    simp [hj.symm]

variable {𝕜 𝓰} in
/-- The parts of a triangular decomposition determined by a basis have natural bases by
construction. -/
noncomputable def ofBasis.basis_part {ι : Type*} [Nontrivial 𝕜] [NoZeroSMulDivisors 𝕜 𝓰]
    (B : Basis ι 𝕜 𝓰) (Bp : SignType → Set ι)
    (Bp_disj : Pairwise (fun ε₁ ε₂ ↦ Disjoint (Bp ε₁) (Bp ε₂)))
    (Bp_cover : ⋃ ε, Bp ε = Set.univ) (ε : SignType) :
    Basis (Bp ε) 𝕜 ((ofBasis B Bp Bp_disj Bp_cover).part ε) :=
  Basis.basis_submodule_span B (Bp ε)

variable {𝕜 𝓰}
variable (tri : TriangularDecomposition 𝕜 𝓰)

/-- The Cartan subalgebra of a given triangular decomposition of a Lie algebra. -/
abbrev cartan := tri.part 0

abbrev upper := tri.part 1

abbrev lower := tri.part (-1)

/-- Weights of a Lie algebra with triangular decomposition are functionals on the
Cartan subalgebra. -/
abbrev weight := tri.cartan →ₗ[𝕜] 𝕜

variable {tri}

/-- The data associated to a weight for the purpose of constructing a highest weight
representation. -/
noncomputable def weightHW (η : weight tri) (i : tri.cartan ⊕ tri.upper) :
    𝓤 𝕜 𝓰 × 𝕜 := match i with
  | Sum.inl H => ⟨ιUEA 𝕜 H, η H⟩
  | Sum.inr E => ⟨ιUEA 𝕜 E, 0⟩

/-- The Verma module of highest weight η. -/
def VermaHW (η : weight tri) :=
  VermaModule (weightHW η)

variable (η : weight tri)

/-- The highest weight vector of the Verma module of highest weight η. -/
noncomputable def VermaHW.hwVec (η : weight tri) : VermaHW η :=
  VermaModule.hwVec _

noncomputable instance (η : weight tri) : AddCommGroup (VermaHW η) :=
  instAddCommGroupVermaModule _

noncomputable instance (η : weight tri) :
    Module (𝓤 𝕜 𝓰) (VermaHW η) :=
  instModuleVermaModule _

noncomputable instance (η : weight tri) :
    Module 𝕜 (VermaHW η) :=
  moduleScalarOfModule 𝕜 (𝓤 𝕜 𝓰) (VermaHW η)

instance (η : weight tri) :
    IsScalarTower 𝕜 (𝓤 𝕜 𝓰) (VermaHW η) :=
  isScalarTowerModuleScalarOfModule 𝕜 (𝓤 𝕜 𝓰) (VermaHW η)

lemma VermaHW.smul_eq_algebraHom_smul {η : weight tri} (r : 𝕜) (v : VermaHW η) :
    r • v = (algebraMap 𝕜 (𝓤 𝕜 𝓰) r) • v :=
  rfl

instance (η : weight tri) :
    SMulCommClass 𝕜 (𝓤 𝕜 𝓰) (VermaHW η) where
  smul_comm r a v := by
    simp_rw [VermaHW.smul_eq_algebraHom_smul]
    simp only [← smul_assoc, smul_eq_mul, Algebra.commutes r a]

lemma VermaHW.hwVec_cyclic (η : weight tri) :
    Submodule.span (𝓤 𝕜 𝓰) {VermaHW.hwVec η} = ⊤ :=
  VermaModule.hwVec_cyclic _

lemma VermaHW.upper_smul_hwVec (η : weight tri) {E : 𝓰} (hE : E ∈ tri.upper) :
    ιUEA 𝕜 E • VermaHW.hwVec η = 0 := by
  simpa [weightHW] using VermaModule.apply_hwVec_eq (weightHW η) (Sum.inr ⟨E, hE⟩)

lemma VermaHW.cartan_smul_hwVec (η : weight tri) {H : 𝓰} (hH : H ∈ tri.cartan) :
    ιUEA 𝕜 H • VermaHW.hwVec η = (η ⟨H, hH⟩) • VermaHW.hwVec η := by
  simpa [weightHW] using VermaModule.apply_hwVec_eq (weightHW η) (Sum.inl ⟨H, hH⟩)

end TriangularDecomposition

end



section VirasoroVerma

--open VirasoroAlgebra

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

def VirasoroAlgebra.indexTri (ε : SignType) : Set (Option ℤ) := match ε with
  | SignType.zero => {none, some 0}
  | SignType.pos => some '' {n : ℤ | 0 < n}
  | SignType.neg => some '' {n : ℤ | n < 0}

lemma VirasoroAlgebra.pairwise_disjoint_indexTri :
    Pairwise fun ε₁ ε₂ ↦ Disjoint (indexTri ε₁) (indexTri ε₂) := by
  intro ε₁ ε₂ h
  simp only [indexTri]
  cases ε₁
  · cases ε₂ <;> aesop
  · cases ε₂
    · aesop
    · aesop
    · apply Set.disjoint_image_image fun k hk l hl ↦ ?_
      by_contra con
      simp only [Set.mem_setOf_eq, Option.some.injEq] at hk hl con
      linarith
  · cases ε₂
    · aesop
    · apply Set.disjoint_image_image fun k hk l hl ↦ ?_
      by_contra con
      simp only [Set.mem_setOf_eq, Option.some.injEq] at hk hl con
      linarith
    · aesop

lemma VirasoroAlgebra.iUnion_indexTri :
    ⋃ ε, indexTri ε = Set.univ := by
  · simp only [indexTri, Set.iUnion_eq_univ_iff]
    intro i
    match i with
    | none => refine ⟨0, by decide⟩
    | some n =>
      by_cases hn0 : n = 0
      · refine ⟨0, by simp [hn0]⟩
      by_cases n_pos : 0 < n
      · refine ⟨1, by simp [n_pos]⟩
      · have n_neg : n < 0 := by grind
        refine ⟨-1, by simp [n_neg]⟩

open VirasoroAlgebra in
/-- The triangular decomposition of the Virasoro algebra with upper and lower (essentially
nilpotent) parts spanned by the `Lₙ` with positive and negative `n`, respectively, and the
Cartan subalgebra spanned by `L₀` and the central element `C`. -/
noncomputable def virasoroTri :
    TriangularDecomposition 𝕜 (VirasoroAlgebra 𝕜) :=
  TriangularDecomposition.ofBasis (basisLC 𝕜) indexTri pairwise_disjoint_indexTri iUnion_indexTri

open VirasoroAlgebra in
lemma virasoroTri_cartan :
    (virasoroTri 𝕜).cartan = Submodule.span 𝕜 {.cgen 𝕜, .lgen 𝕜 0} := by
  simp only [virasoroTri, indexTri, TriangularDecomposition.ofBasis, TriangularDecomposition.cartan]
  congr 1
  aesop

open VirasoroAlgebra in
lemma virasoroTri_upper :
    (virasoroTri 𝕜).upper = Submodule.span 𝕜 ((fun n ↦ lgen 𝕜 n) '' {n | 0 < n}) := by
  simp only [virasoroTri, indexTri, TriangularDecomposition.upper, TriangularDecomposition.ofBasis]
  congr 1
  aesop

open VirasoroAlgebra in
lemma virasoroTri_lower :
    (virasoroTri 𝕜).lower = Submodule.span 𝕜 ((fun n ↦ lgen 𝕜 n) '' {n | n < 0}) := by
  simp only [virasoroTri, indexTri, TriangularDecomposition.ofBasis, TriangularDecomposition.lower]
  congr 1
  aesop

open VirasoroAlgebra in
noncomputable def virasoroTri_cartan_basis :
    Basis ({none, some 0} : Set (Option ℤ)) 𝕜 (virasoroTri 𝕜).cartan :=
  TriangularDecomposition.ofBasis.basis_part (VirasoroAlgebra.basisLC 𝕜) indexTri
    pairwise_disjoint_indexTri iUnion_indexTri 0

/-- The highest weight of Virasoro algebra determined by the central charge `c` (`C`-eigenvalue)
and conformal weight `h` (`L₀`-eigenvalue). -/
noncomputable def VirasoroAlgebra.hw (c h : 𝕜) :
    (virasoroTri 𝕜).cartan →ₗ[𝕜] 𝕜 :=
  (virasoroTri_cartan_basis 𝕜).constr (M' := 𝕜) 𝕜 (fun i ↦ if i.val = none then c else h)

/-- The Virasoro generator `C` as an element of the Cartan subalgebra. -/
noncomputable def virasoroTri_cgen : (virasoroTri 𝕜).part 0 :=
  ⟨.cgen 𝕜, Submodule.mem_span_of_mem (by simp [VirasoroAlgebra.indexTri])⟩

/-- The Virasoro generator `L₀` as an element of the Cartan subalgebra. -/
noncomputable def virasoroTri_lzero : (virasoroTri 𝕜).part 0 :=
  ⟨.lgen 𝕜 0, Submodule.mem_span_of_mem (by simp [VirasoroAlgebra.indexTri])⟩

@[simp] lemma virasoroTri_cgen_val :
    (virasoroTri_cgen 𝕜).val = .cgen 𝕜 :=
  rfl

@[simp] lemma virasoroTri_lzero_val :
    (virasoroTri_lzero 𝕜).val = .lgen 𝕜 0 :=
  rfl

open VirasoroAlgebra in
lemma virasoroTri_cartan_basis_none_eq_cgen :
    (virasoroTri_cartan_basis 𝕜) ⟨none, Set.mem_insert none {some 0}⟩ = virasoroTri_cgen 𝕜 := by
  ext
  simp only [virasoroTri_cartan_basis, TriangularDecomposition.ofBasis.basis_part, indexTri,
             virasoroTri_cgen_val]
  convert (basisLC 𝕜).basis_submodule_span_apply {none, some 0} ⟨none, Set.mem_insert none {some 0}⟩
  simp

open VirasoroAlgebra in
lemma virasoroTri_cartan_basis_some_eq_lzero :
    (virasoroTri_cartan_basis 𝕜) ⟨some 0, by exact Set.mem_insert_of_mem none rfl⟩
      = virasoroTri_lzero 𝕜 := by
  ext
  simp only [virasoroTri_cartan_basis, TriangularDecomposition.ofBasis.basis_part, indexTri,
             virasoroTri_lzero_val]
  convert (basisLC 𝕜).basis_submodule_span_apply {none, some 0}
          ⟨some 0, Set.mem_insert_of_mem none rfl⟩
  simp

lemma virasoroTri_cgen_mem_cartan :
    .cgen 𝕜 ∈ (virasoroTri 𝕜).cartan := by
  simpa only [virasoroTri_cartan] using Submodule.mem_span_of_mem (by simp)

lemma virasoroTri_lgen_zero_mem_cartan :
    .lgen 𝕜 0 ∈ (virasoroTri 𝕜).cartan := by
  simpa only [virasoroTri_cartan] using Submodule.mem_span_of_mem (by simp)

lemma virasoroTri_lgen_pos_mem_upper {n : ℤ} (n_pos : 0 < n) :
    .lgen 𝕜 n ∈ (virasoroTri 𝕜).upper := by
  simp only [virasoroTri_upper]
  apply Submodule.mem_span_of_mem
  exact (Set.mem_image ..).mpr ⟨n, ⟨n_pos, rfl⟩⟩

lemma VirasoroAlgebra.hw_apply_cgen (c h : 𝕜) :
    hw 𝕜 c h (virasoroTri_cgen 𝕜) = c := by
  rw [← virasoroTri_cartan_basis_none_eq_cgen]
  simp only [hw, Basis.constr_apply_fintype]
  simp only [Basis.equivFun_self, smul_eq_mul, mul_ite, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ⟨none, Set.mem_insert none {some 0}⟩]
  · simp
  · intro j _ hj
    simp [hj.symm, show ¬ (j : Option ℤ) = none by aesop]
  · simp

lemma VirasoroAlgebra.hw_apply_lzero (c h : 𝕜) :
    hw 𝕜 c h (virasoroTri_lzero 𝕜) = h := by
  rw [← virasoroTri_cartan_basis_some_eq_lzero]
  simp only [hw, Basis.constr_apply_fintype]
  simp only [Basis.equivFun_self, smul_eq_mul, mul_ite, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ⟨some 0, by exact Set.mem_insert_of_mem none rfl⟩]
  · simp
  · intro j _ hj
    simp [hj.symm]
  · simp

/-- The Verma module for the Virasoso algebra with central charge `c` and conformal weight `h`. -/
abbrev VirasoroVerma (c h : 𝕜) := (virasoroTri 𝕜).VermaHW (VirasoroAlgebra.hw 𝕜 c h)

/-- The highest weight vector in the Verma module for the Virasoso algebra with central charge `c`
and conformal weight `h`. -/
noncomputable abbrev VirasoroVerma.hwVec (c h : 𝕜) :=
   TriangularDecomposition.VermaHW.hwVec (VirasoroAlgebra.hw 𝕜 c h)

lemma VirasoroVerma.hwVec_cyclic (c h : 𝕜) :
    Submodule.span (𝓤 𝕜 (VirasoroAlgebra 𝕜)) {VirasoroVerma.hwVec 𝕜 c h} = ⊤ :=
  VermaModule.hwVec_cyclic ..

lemma VirasoroVerma.lgen_pos_hwVec (c h : 𝕜) {n : ℤ} (n_pos : 0 < n) :
    ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 n) • hwVec 𝕜 c h = 0 :=
  TriangularDecomposition.VermaHW.upper_smul_hwVec
    (VirasoroAlgebra.hw 𝕜 c h) (E := .lgen 𝕜 n) (virasoroTri_lgen_pos_mem_upper 𝕜 n_pos)

lemma VirasoroVerma.lgen_zero_hwVec (c h : 𝕜) :
    ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 0) • hwVec 𝕜 c h = h • hwVec 𝕜 c h := by
  convert TriangularDecomposition.VermaHW.cartan_smul_hwVec
          (VirasoroAlgebra.hw 𝕜 c h) (H := .lgen 𝕜 0) (virasoroTri_lgen_zero_mem_cartan 𝕜)
  exact (VirasoroAlgebra.hw_apply_lzero 𝕜 c h).symm

lemma VirasoroVerma.cgen_hwVec (c h : 𝕜) :
    ιUEA 𝕜 (VirasoroAlgebra.cgen 𝕜) • hwVec 𝕜 c h = c • hwVec 𝕜 c h := by
  convert TriangularDecomposition.VermaHW.cartan_smul_hwVec
          (VirasoroAlgebra.hw 𝕜 c h) (H := .cgen 𝕜) (virasoroTri_cgen_mem_cartan 𝕜)
  exact (VirasoroAlgebra.hw_apply_cgen 𝕜 c h).symm

lemma VirasoroVerma.cgen_smul (c h : 𝕜) (v : VirasoroVerma 𝕜 c h) :
    ιUEA 𝕜 (VirasoroAlgebra.cgen 𝕜) • v = c • v :=
  UniversalEnvelopingAlgebra.smul_eq_of_cyclic_of_forall_lie_eq_zero
    _ _ (fun _ ↦ rfl) (hwVec_cyclic 𝕜 c h) (cgen_hwVec 𝕜 c h) v

end VirasoroVerma



end VirasoroProject
