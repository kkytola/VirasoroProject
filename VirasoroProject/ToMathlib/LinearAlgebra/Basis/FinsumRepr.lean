import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.DFinsupp
import VirasoroProject.ToMathlib.LinearAlgebra.Finsupp.Supported

lemma smul_support_subset_left {R M ι : Type*} [Semiring R]
    [AddCommGroup M] [Module R M] (v : ι → M) (cf : ι → R) :
    (fun i ↦ cf i • v i).support ⊆ cf.support := by
  simp only [Function.support_subset_iff, ne_eq, Function.mem_support]
  intro i
  rw [not_imp_not]
  intro hcf
  simp [hcf]

namespace Module.Basis

lemma iSupIndep_submodule_span_of_pairwise_disjoint
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

lemma finsum_repr_smul_basis {R M ι : Type*} [Semiring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] (B : Basis ι R M) (v : M) :
    ∑ᶠ i, B.repr v i • B i = v := by
  have obs : (Function.support fun i ↦ B.repr v i • B i).Finite := by
    apply (Finsupp.hasFiniteSupport (B.repr v)).subset
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi ⊢
    exact fun h ↦ hi (by rw [h, zero_smul])
  rw [finsum_eq_sum _ obs]
  apply B.repr.injective
  rw [map_sum]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
  ext i
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ j_ne_i
    simp [j_ne_i]
  · intro hi
    exact (eq_zero_or_eq_zero_of_smul_eq_zero (by simpa using hi)).resolve_right (B.ne_zero i)

lemma repr_finsum {R M ι : Type*} [Semiring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] (B : Basis ι R M) (cf : ι →₀ R) :
    B.repr (∑ᶠ i, cf i • B i) = cf := by
  have key := B.finsum_repr_smul_basis (B.repr.symm cf)
  rw [B.repr.apply_symm_apply] at key
  rw [key, B.repr.apply_symm_apply]

lemma repr_finsum_mem_eq_ite {R M ι : Type*} [Semiring R] [Nontrivial R]
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

noncomputable def basis_submodule_span {R M ι : Type*} [Semiring R] [Nontrivial R]
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
      · exact cf₁.hasFiniteSupport.subset <| smul_support_subset_left ..
      · exact cf₂.hasFiniteSupport.subset <| smul_support_subset_left ..
    map_smul' r cf := by
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_assoc, RingHom.id_apply, SetLike.mk_smul_mk,
                 Subtype.mk.injEq]
      exact (smul_finsum' r (cf.hasFiniteSupport.subset <| smul_support_subset_left ..)).symm }
  have fog : f ∘ g = id := by
    funext cf
    ext i
    simp only [f, g, LinearMap.coe_mk, AddHom.coe_mk]
    classical
    have aux := B.repr_finsum_mem_eq_ite cf.extendDomain I i
    simp only [Finsupp.extendDomain_apply, dite_smul, zero_smul, Subtype.coe_prop, ↓reduceIte,
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
    map_add' x y := f.map_add x y
    map_smul' m x := LinearMap.CompatibleSMul.map_smul f m x
    invFun := g
    left_inv := by exact congrFun gof
    right_inv := by exact congrFun fog
  }⟩

-- TODO: To Mathlib?
@[simp] lemma basis_submodule_span_apply {R M ι : Type*}
    [Semiring R] [Nontrivial R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
    (B : Basis ι R M) (I : Set ι) (i : I) :
    B.basis_submodule_span I i = B i.val := by
  simp only [Basis.basis_submodule_span, LinearMap.coe_mk, AddHom.coe_mk, Basis.coe_ofRepr,
             LinearEquiv.coe_symm_mk]
  rw [finsum_eq_single _ i]
  · simp
  · intro j hj
    simp [hj.symm]

end Module.Basis
