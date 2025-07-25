/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib
import VirasoroProject.VermaModule
import VirasoroProject.VirasoroAlgebra
import VirasoroProject.ToMathlib.LinearAlgebra.Basis.FinsumRepr



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

variable {𝕜 𝓰} in
def ofBasis {ι : Type*} [Nontrivial 𝕜] [NoZeroSMulDivisors 𝕜 𝓰]
    (B : Basis ι 𝕜 𝓰) (Bp : SignType → Set ι)
    (Bp_disj : Pairwise (fun ε₁ ε₂ ↦ Disjoint (Bp ε₁) (Bp ε₂)))
    (Bp_cover : ⋃ ε, Bp ε = Set.univ) :
    TriangularDecomposition 𝕜 𝓰 where
  part ε := Submodule.span 𝕜 (B '' Bp ε)
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
