/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib
import VirasoroProject.VermaModule
import VirasoroProject.VirasoroAlgebra
import VirasoroProject.LieVerma
import VirasoroProject.IndexTri



namespace VirasoroProject

section HasCentralCharge

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
variable (M : Type*) [AddCommGroup M] [Module 𝕜 M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M]

abbrev HasCentralCharge (c : 𝕜) := HasCentralValue 𝕜 (VirasoroAlgebra 𝕜) M (.cgen _) c

@[simp] lemma HasCentralCharge.cgen_smul {c : 𝕜} [HasCentralCharge 𝕜 M c] (v : M) :
    ιUEA 𝕜 (VirasoroAlgebra.cgen 𝕜) • v = c • v :=
  HasCentralValue.central_smul ..

end HasCentralCharge

section VirasoroVerma

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

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
  ⟨.cgen 𝕜, Submodule.mem_span_of_mem (by simp [indexTri])⟩

/-- The Virasoro generator `L₀` as an element of the Cartan subalgebra. -/
noncomputable def virasoroTri_lzero : (virasoroTri 𝕜).part 0 :=
  ⟨.lgen 𝕜 0, Submodule.mem_span_of_mem (by simp [indexTri])⟩

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

/-- The Virasoro Verma module with central charge `c` and conformal weight `h` has central
charge `c`. -/
instance (c h : 𝕜) : HasCentralCharge 𝕜 (VirasoroVerma 𝕜 c h) c :=
  ⟨fun v ↦ VirasoroVerma.cgen_smul 𝕜 c h v⟩

private lemma upper_smul_eq_zero_of_forall_pos_lgen_smul_eq_zero (c h : 𝕜)
    {M : Type*} [AddCommGroup M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M] {v : M}
    (hwv_lpos : ∀ n > 0, ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 n) • v = 0) :
    ∀ {E} (hE : E ∈ (virasoroTri 𝕜).upper), (ιUEA 𝕜) E • v = 0 := by
  simp only [virasoroTri_upper]
  apply Submodule.span_induction
  · simpa only [Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
                forall_apply_eq_imp_iff₂] using hwv_lpos
  · simp
  · intro E₁ E₂ _ _ hE₁ hE₂
    simp only [LieHom.map_add, add_smul, hE₁, hE₂, add_zero]
  · intro r E _ hE
    have hE' : algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) r • (ιUEA 𝕜 E • v) = 0 := by
      simp only [hE, smul_zero]
    simp only [LieHom.map_smul, ← hE', ← smul_assoc]
    congr 1
    exact algebra_compatible_smul (𝓤 𝕜 (VirasoroAlgebra 𝕜)) r ((ιUEA 𝕜) E)

private lemma cartan_smul_eq_of_cgen_smul_eq_of_lzero_smul_eq {c h : 𝕜}
    {M : Type*} [AddCommGroup M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M] {v : M}
    (hwv_c : ιUEA 𝕜 (VirasoroAlgebra.cgen 𝕜) • v
              = (algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) c • v))
    (hwv_lzero : ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 0) • v
              = (algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) h • v)) :
    ∀ {H} (hH : H ∈ (virasoroTri 𝕜).cartan) ,
      (ιUEA 𝕜) H • v
        = (algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜))) ((VirasoroAlgebra.hw 𝕜 c h) ⟨H, hH⟩) • v := by
  simp only [virasoroTri_cartan]
  apply Submodule.span_induction
  · intro X hX
    cases' hX with X_eq X_eq'
    · simp only [X_eq, hwv_c]
      congr 2
      exact (VirasoroAlgebra.hw_apply_cgen 𝕜 c h).symm
    · simp only [Set.mem_singleton_iff] at X_eq'
      simp only [X_eq', hwv_lzero]
      congr 2
      exact (VirasoroAlgebra.hw_apply_lzero 𝕜 c h).symm
  · simp only [LieHom.map_zero, zero_smul]
    convert (zero_smul ..).symm
    convert algebraMap.coe_zero
    exact LinearMap.map_zero (VirasoroAlgebra.hw 𝕜 c h)
  · intro H₁ H₂ _ _ hH₁ hH₂
    simp only [LieHom.map_add, add_smul, hH₁, hH₂]
    rw [← add_smul, ← map_add, ← map_add]
    rfl
  · intro r H H_mem hH
    have aux : (r • (ιUEA 𝕜) H) • v
                = algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) r • ((ιUEA 𝕜) H • v) := by
      simp only [← smul_assoc, smul_eq_mul, Algebra.smul_def r ((ιUEA 𝕜) H)]
    simp only [LieHom.map_smul, aux, hH, ← smul_assoc]
    congr 1
    rw [smul_eq_mul, ← map_mul]
    congr 1
    rw [← smul_eq_mul, ← map_smul]
    rfl

noncomputable def VirasoroVerma.universalMap {c h : 𝕜}
    (M : Type*) [AddCommGroup M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M] {hwv : M}
    (hwv_c : ιUEA 𝕜 (VirasoroAlgebra.cgen 𝕜) • hwv
              = (algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) c • hwv))
    (hwv_lzero : ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 0) • hwv
              = (algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) h • hwv))
    (hwv_lpos : ∀ n > 0, ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 n) • hwv = 0) :
    VirasoroVerma 𝕜 c h →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] M := by
  apply @TriangularDecomposition.VermaHW.universalMap 𝕜 _ (VirasoroAlgebra 𝕜) _ _ (virasoroTri 𝕜)
        (VirasoroAlgebra.hw _ c h) M _ _ hwv ?_ ?_
  · exact cartan_smul_eq_of_cgen_smul_eq_of_lzero_smul_eq 𝕜 hwv_c hwv_lzero
  · exact upper_smul_eq_zero_of_forall_pos_lgen_smul_eq_zero 𝕜 c h hwv_lpos

lemma VirasoroVerma.universalMap_hwVec (c h : 𝕜)
    (M : Type*) [AddCommGroup M] [Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) M] {hwv : M}
    (hwv_c : ιUEA 𝕜 (VirasoroAlgebra.cgen 𝕜) • hwv
              = (algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) c • hwv))
    (hwv_lzero : ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 0) • hwv
              = (algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) h • hwv))
    (hwv_lpos : ∀ n > 0, ιUEA 𝕜 (VirasoroAlgebra.lgen 𝕜 n) • hwv = 0) :
    VirasoroVerma.universalMap 𝕜 M hwv_c hwv_lzero hwv_lpos (hwVec 𝕜 c h) = hwv :=
  TriangularDecomposition.VermaHW.universalMap_hwVec ..

end VirasoroVerma

end VirasoroProject
