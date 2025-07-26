/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib
import VirasoroProject.Commutator
import VirasoroProject.VermaModule
import VirasoroProject.HeisenbergAlgebra
import VirasoroProject.LieVerma
import VirasoroProject.IndexTri

namespace VirasoroProject



section HeisenbergVerma

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

open HeisenbergAlgebra in
/-- The triangular decomposition of the Heisenberg algebra with upper and lower (essentially
nilpotent) parts spanned by the `Jₖ` with positive and negative `k`, respectively, and the
Cartan subalgebra spanned by `J₀` and the central element `K`. -/
noncomputable def heisenbergTri :
    TriangularDecomposition 𝕜 (HeisenbergAlgebra 𝕜) :=
  TriangularDecomposition.ofBasis (basisJK 𝕜) indexTri pairwise_disjoint_indexTri iUnion_indexTri

open HeisenbergAlgebra TriangularDecomposition in
lemma heisenbergTri_cartan :
    (heisenbergTri 𝕜).cartan = Submodule.span 𝕜 {.kgen 𝕜, .jgen 𝕜 0} := by
  simp only [heisenbergTri, indexTri, ofBasis, cartan]
  congr 1
  aesop

open HeisenbergAlgebra TriangularDecomposition in
lemma heisenbergTri_upper :
    (heisenbergTri 𝕜).upper = Submodule.span 𝕜 ((fun n ↦ jgen 𝕜 n) '' {n | 0 < n}) := by
  simp only [heisenbergTri, indexTri, ofBasis, upper]
  congr 1
  aesop

open HeisenbergAlgebra TriangularDecomposition in
lemma heisenbergTri_lower :
    (heisenbergTri 𝕜).lower = Submodule.span 𝕜 ((fun n ↦ jgen 𝕜 n) '' {n | n < 0}) := by
  simp only [heisenbergTri, indexTri, ofBasis, lower]
  congr 1
  aesop

open HeisenbergAlgebra in
noncomputable def heisenbergTri_cartan_basis :
    Basis ({none, some 0} : Set (Option ℤ)) 𝕜 (heisenbergTri 𝕜).cartan :=
  TriangularDecomposition.ofBasis.basis_part (HeisenbergAlgebra.basisJK 𝕜) indexTri
    pairwise_disjoint_indexTri iUnion_indexTri 0

/-- The highest weight of Heisenberg algebra determined by charge `α` (`J₀`-eigenvalue).
The `K`-eigenvalue is by convention normalized to `1` by default. -/
noncomputable def HeisenbergAlgebra.hw (α : 𝕜) :
    (heisenbergTri 𝕜).cartan →ₗ[𝕜] 𝕜 :=
  (heisenbergTri_cartan_basis 𝕜).constr (M' := 𝕜) 𝕜 (fun i ↦ if i.val = none then 1 else α)

/-- The Heisenberg generator `C` as an element of the Cartan subalgebra. -/
noncomputable def heisenbergTri_kgen : (heisenbergTri 𝕜).part 0 :=
  ⟨.kgen 𝕜, Submodule.mem_span_of_mem (by simp [indexTri])⟩

/-- The Heisenberg generator `L₀` as an element of the Cartan subalgebra. -/
noncomputable def heisenbergTri_jzero : (heisenbergTri 𝕜).part 0 :=
  ⟨.jgen 𝕜 0, Submodule.mem_span_of_mem (by simp [indexTri])⟩

@[simp] lemma heisenbergTri_kgen_val :
    (heisenbergTri_kgen 𝕜).val = .kgen 𝕜 :=
  rfl

@[simp] lemma heisenbergTri_jzero_val :
    (heisenbergTri_jzero 𝕜).val = .jgen 𝕜 0 :=
  rfl

open HeisenbergAlgebra in
lemma heisenbergTri_cartan_basis_none_eq_kgen :
    (heisenbergTri_cartan_basis 𝕜) ⟨none, Set.mem_insert none {some 0}⟩ = heisenbergTri_kgen 𝕜 := by
  ext
  simp only [heisenbergTri_cartan_basis, TriangularDecomposition.ofBasis.basis_part, indexTri,
             heisenbergTri_kgen_val]
  convert (basisJK 𝕜).basis_submodule_span_apply {none, some 0} ⟨none, Set.mem_insert none {some 0}⟩
  simp

open HeisenbergAlgebra in
lemma heisenbergTri_cartan_basis_some_eq_jzero :
    (heisenbergTri_cartan_basis 𝕜) ⟨some 0, by exact Set.mem_insert_of_mem none rfl⟩
      = heisenbergTri_jzero 𝕜 := by
  ext
  simp only [heisenbergTri_cartan_basis, TriangularDecomposition.ofBasis.basis_part, indexTri,
             heisenbergTri_jzero_val]
  convert (basisJK 𝕜).basis_submodule_span_apply {none, some 0}
          ⟨some 0, Set.mem_insert_of_mem none rfl⟩
  simp

lemma heisenbergTri_kgen_mem_cartan :
    .kgen 𝕜 ∈ (heisenbergTri 𝕜).cartan := by
  simpa only [heisenbergTri_cartan] using Submodule.mem_span_of_mem (by simp)

lemma heisenbergTri_jgen_zero_mem_cartan :
    .jgen 𝕜 0 ∈ (heisenbergTri 𝕜).cartan := by
  simpa only [heisenbergTri_cartan] using Submodule.mem_span_of_mem (by simp)

lemma heisenbergTri_jgen_pos_mem_upper {n : ℤ} (n_pos : 0 < n) :
    .jgen 𝕜 n ∈ (heisenbergTri 𝕜).upper := by
  simp only [heisenbergTri_upper]
  apply Submodule.mem_span_of_mem
  exact (Set.mem_image ..).mpr ⟨n, ⟨n_pos, rfl⟩⟩

lemma HeisenbergAlgebra.hw_apply_kgen (α : 𝕜) :
    hw 𝕜 α (heisenbergTri_kgen 𝕜) = 1 := by
  rw [← heisenbergTri_cartan_basis_none_eq_kgen]
  simp only [hw, Basis.constr_apply_fintype]
  simp only [Basis.equivFun_self, smul_eq_mul, mul_ite, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ⟨none, Set.mem_insert none {some 0}⟩]
  · simp
  · intro j _ hj
    simp [hj.symm, show ¬ (j : Option ℤ) = none by aesop]
  · simp

lemma HeisenbergAlgebra.hw_apply_jzero (α : 𝕜) :
    hw 𝕜 α (heisenbergTri_jzero 𝕜) = α := by
  rw [← heisenbergTri_cartan_basis_some_eq_jzero]
  simp only [hw, Basis.constr_apply_fintype]
  simp only [Basis.equivFun_self, smul_eq_mul, mul_ite, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ⟨some 0, by exact Set.mem_insert_of_mem none rfl⟩]
  · simp
  · intro j _ hj
    simp [hj.symm]
  · simp

/-- The Verma module for the Heisenberg algebra with charge `α`. -/
abbrev HeisenbergVerma (α : 𝕜) := (heisenbergTri 𝕜).VermaHW (HeisenbergAlgebra.hw 𝕜 α)

/-- The highest weight vector in the Verma module for the Heisenberg algebra with charge `α`. -/
noncomputable abbrev HeisenbergVerma.hwVec (α : 𝕜) :=
   TriangularDecomposition.VermaHW.hwVec (HeisenbergAlgebra.hw 𝕜 α)

lemma HeisenbergVerma.hwVec_cyclic (α : 𝕜) :
    Submodule.span (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) {HeisenbergVerma.hwVec 𝕜 α} = ⊤ :=
  VermaModule.hwVec_cyclic ..

/-- `Jₖ • vacuum(α) = 0` for `k > 0` -/
lemma HeisenbergVerma.jgen_pos_hwVec (α : 𝕜) {k : ℤ} (k_pos : 0 < k) :
    ιUEA 𝕜 (HeisenbergAlgebra.jgen 𝕜 k) • hwVec 𝕜 α = 0 :=
  TriangularDecomposition.VermaHW.upper_smul_hwVec
    (HeisenbergAlgebra.hw 𝕜 α) (E := .jgen 𝕜 k) (heisenbergTri_jgen_pos_mem_upper 𝕜 k_pos)

lemma HeisenbergVerma.jgen_zero_hwVec (α : 𝕜) :
    ιUEA 𝕜 (HeisenbergAlgebra.jgen 𝕜 0) • hwVec 𝕜 α = α • hwVec 𝕜 α := by
  convert TriangularDecomposition.VermaHW.cartan_smul_hwVec
          (HeisenbergAlgebra.hw 𝕜 α) (H := .jgen 𝕜 0) (heisenbergTri_jgen_zero_mem_cartan 𝕜)
  exact (HeisenbergAlgebra.hw_apply_jzero 𝕜 α).symm

lemma HeisenbergVerma.kgen_hwVec (α : 𝕜) :
    ιUEA 𝕜 (HeisenbergAlgebra.kgen 𝕜) • hwVec 𝕜 α = hwVec 𝕜 α := by
  have key := TriangularDecomposition.VermaHW.cartan_smul_hwVec
          (HeisenbergAlgebra.hw 𝕜 α) (H := .kgen 𝕜) (heisenbergTri_kgen_mem_cartan 𝕜)
  rw [← heisenbergTri_kgen, HeisenbergAlgebra.hw_apply_kgen, one_smul] at key
  convert key

/-- `J₀ • v = α • v` for all `v` in `HeisenbergVerma 𝕜 α` -/
lemma HeisenbergVerma.kgen_smul (α : 𝕜) (v : HeisenbergVerma 𝕜 α) :
    ιUEA 𝕜 (HeisenbergAlgebra.kgen 𝕜) • v = v := by
  have aux : ιUEA 𝕜 (HeisenbergAlgebra.kgen 𝕜) • hwVec 𝕜 α = (1 : 𝕜) • hwVec 𝕜 α := by
    rw [kgen_hwVec 𝕜 α, one_smul]
  simpa using UniversalEnvelopingAlgebra.smul_eq_of_cyclic_of_forall_lie_eq_zero
    _ _ (fun _ ↦ rfl) (hwVec_cyclic 𝕜 α) aux v

/-- `J₀ • v = α • v` for all `v` in `HeisenbergVerma 𝕜 α` -/
@[simp] lemma HeisenbergVerma.jgen_zero_smul (α : 𝕜) (v : HeisenbergVerma 𝕜 α) :
    (ιUEA 𝕜 (HeisenbergAlgebra.jgen 𝕜 0)) • v = α • v := by
  exact UniversalEnvelopingAlgebra.smul_eq_of_cyclic_of_forall_lie_eq_zero 𝕜
    (HeisenbergAlgebra 𝕜) (Z := .jgen 𝕜 0) (ζ := α) (HeisenbergAlgebra.lie_jgen_zero _)
    (hwVec_cyclic 𝕜 α) (jgen_zero_hwVec 𝕜 α) v

open Filter in
lemma HeisenbergAlgebra.uea_eventually_commute_jgen (a : 𝓤 𝕜 (HeisenbergAlgebra 𝕜)) :
    ∀ᶠ k in atTop, Commute (ιUEA 𝕜 (jgen 𝕜 k)) a := by
  apply UniversalEnvelopingAlgebra.induction 𝕜 _
    (C := fun a' ↦ ∀ᶠ k in atTop, Commute (ιUEA 𝕜 (jgen 𝕜 k)) a')
  · intro r
    filter_upwards [Ioi_mem_atTop 0] with k k_pos
    exact (Algebra.commutes r _).symm
  · let whole := Submodule.span 𝕜 (Set.range (basisJK 𝕜))
    suffices ∀ X ∈ whole, ∀ᶠ k in atTop,
        Commute (ιUEA 𝕜 (jgen 𝕜 k)) (ιUEA 𝕜 X) from
      fun X ↦ this X (by simp [whole])
    apply Submodule.span_induction
    · intro Z ⟨i, hiZ⟩
      match i with
      | none =>
        simp only [← hiZ, basisJK_none]
        filter_upwards [Ioi_mem_atTop 0] with k k_pos
        exact (UniversalEnvelopingAlgebra.central_of_forall_lie_eq_zero 𝕜 (HeisenbergAlgebra 𝕜)
                (congrFun rfl) ((ιUEA 𝕜) (jgen 𝕜 k))).symm
      | some l =>
        simp only [← hiZ, basisJK_some]
        filter_upwards [Ioi_mem_atTop |l|] with k hk
        rw [commute_iff_lie_eq, ← LieHom.map_lie]
        have obs : ¬ k + l = 0 := by
          simp only [Set.mem_Ioi, abs_lt] at hk
          grind
        simp [lie_jgen, obs]
    · simp
    · intro a b a_mem b_mem ha hb
      filter_upwards [ha, hb] with k hka hkb
      simpa only [LieHom.map_add] using Commute.add_right hka hkb
    · intro r a a_mem ha
      filter_upwards [ha] with k hka
      simpa only [LieHom.map_smul] using Commute.smul_right hka _
  · intro a b ha hb
    filter_upwards [ha, hb] with k hka hkb using Commute.mul_right hka hkb
  · intro a b ha hb
    filter_upwards [ha, hb] with k hka hkb using Commute.add_right hka hkb

open Filter HeisenbergAlgebra in
lemma HeisenbergVerma.eventually_jgen_smul_eq_zero (α : 𝕜) (v : HeisenbergVerma 𝕜 α) :
    ∀ᶠ k in atTop, (ιUEA 𝕜 (jgen 𝕜 k)) • v = 0 := by
  have aux : v ∈ Submodule.span (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) {hwVec 𝕜 α} := by
    simp [hwVec_cyclic 𝕜 α]
  obtain ⟨a, hav⟩ := Submodule.mem_span_singleton.mp aux
  filter_upwards [uea_eventually_commute_jgen _ a, Ioi_mem_atTop 0] with k hk k_pos
  -- `calcify`?
  rw [← hav, ← mul_smul]
  rw [show _ * a = a * _ from hk]
  rw [mul_smul]
  rw [jgen_pos_hwVec _ _ k_pos, smul_zero]

end HeisenbergVerma



section Fock_space

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

/-- The indexed collection of Heisenberg (associative) algebra generators
of nonnegative index (K, J₀, J₁, J₂, ...) together with the scalars by which
they act on the vacuum of the charged Fock space of charge α. -/
noncomputable def HeisenbergAlgebra.chargedFockHW (α : 𝕜) (i : Option ℕ) :
    𝓤 𝕜 (HeisenbergAlgebra 𝕜) × 𝕜 := match i with
  | none => ⟨ιUEA 𝕜 (kgen 𝕜), 1⟩
  | some 0 => ⟨ιUEA 𝕜 (jgen 𝕜 0), α⟩
  | some k => ⟨ιUEA 𝕜 (jgen 𝕜 k), 0⟩

/-- The charged Fock space (module over the Heisenberg algebra) of charge α. -/
def ChargedFockSpace (α : 𝕜) :=
  VermaModule (HeisenbergAlgebra.chargedFockHW 𝕜 α)

/-- The vacuum vector of the charged Fock space (module over the Heisenberg algebra) of charge α. -/
noncomputable def ChargedFockSpace.vacuum (α : 𝕜) : ChargedFockSpace 𝕜 α :=
  VermaModule.hwVec (HeisenbergAlgebra.chargedFockHW 𝕜 α)

noncomputable instance (α : 𝕜) : AddCommGroup (ChargedFockSpace 𝕜 α) :=
  instAddCommGroupVermaModule _

noncomputable instance (α : 𝕜) :
    Module (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) (ChargedFockSpace 𝕜 α) :=
  instModuleVermaModule _

noncomputable instance (α : 𝕜) :
    Module 𝕜 (ChargedFockSpace 𝕜 α) :=
  moduleScalarOfModule 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) (ChargedFockSpace 𝕜 α)

instance (α : 𝕜) :
    IsScalarTower 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) (ChargedFockSpace 𝕜 α) :=
  isScalarTowerModuleScalarOfModule 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) (ChargedFockSpace 𝕜 α)

lemma ChargedFockSpace.smul_eq_algebraHom_smul {α : 𝕜} (r : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    r • v = (algebraMap 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) r) • v :=
  rfl

instance (α : 𝕜) :
    SMulCommClass 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) (ChargedFockSpace 𝕜 α) where
  smul_comm r a v := by
    simp_rw [ChargedFockSpace.smul_eq_algebraHom_smul]
    simp only [← smul_assoc, smul_eq_mul, Algebra.commutes r a]

lemma ChargedFockSpace.vacuum_cyclic (α : 𝕜) :
    Submodule.span (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) {vacuum 𝕜 α} = ⊤ :=
  VermaModule.hwVec_cyclic _

/-- `K • vacuum(α) = vacuum(α)` -/
lemma ChargedFockSpace.kgen_vacuum (α : 𝕜) :
    (ιUEA 𝕜 (HeisenbergAlgebra.kgen 𝕜)) • vacuum 𝕜 α = vacuum 𝕜 α := by
  convert VermaModule.apply_hwVec_eq (HeisenbergAlgebra.chargedFockHW 𝕜 α) none
  simp [HeisenbergAlgebra.chargedFockHW]
  rfl

/-- `K • v = v` for all `v` in `ChargedFockSpace 𝕜 α` -/
@[simp] lemma ChargedFockSpace.kgen_smul (α : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    (ιUEA 𝕜 (HeisenbergAlgebra.kgen 𝕜)) • v = v := by
  simpa using UniversalEnvelopingAlgebra.smul_eq_of_cyclic_of_forall_lie_eq_zero 𝕜
    (HeisenbergAlgebra 𝕜) (Z := .kgen 𝕜) (ζ := 1) (HeisenbergAlgebra.lie_kgen _)
    (vacuum_cyclic 𝕜 α) (by simpa only [map_one, one_smul] using kgen_vacuum 𝕜 α) v

/-- `J₀ • vacuum(α) = α • vacuum(α)` -/
lemma ChargedFockSpace.jgen_zero_vacuum (α : 𝕜) :
    (ιUEA 𝕜 (HeisenbergAlgebra.jgen 𝕜 0)) • vacuum 𝕜 α = α • vacuum 𝕜 α :=
  VermaModule.apply_hwVec_eq (HeisenbergAlgebra.chargedFockHW 𝕜 α) (some 0)

/-- `J₀ • v = α • v` for all `v` in `ChargedFockSpace 𝕜 α` -/
@[simp] lemma ChargedFockSpace.jgen_zero_smul (α : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    (ιUEA 𝕜 (HeisenbergAlgebra.jgen 𝕜 0)) • v = α • v := by
  exact UniversalEnvelopingAlgebra.smul_eq_of_cyclic_of_forall_lie_eq_zero 𝕜
    (HeisenbergAlgebra 𝕜) (Z := .jgen 𝕜 0) (ζ := α) (HeisenbergAlgebra.lie_jgen_zero _)
    (vacuum_cyclic 𝕜 α) (jgen_zero_vacuum 𝕜 α) v

/-- `Jₖ • vacuum(α) = 0` for `k > 0` -/
lemma ChargedFockSpace.jgen_pos_vacuum (α : 𝕜) {k : ℤ} (k_pos : 0 < k) :
    (ιUEA 𝕜 (HeisenbergAlgebra.jgen 𝕜 k)) • vacuum 𝕜 α = 0 := by
  set n := Int.toNat k with def_n
  rw [← show (n : ℤ) = k by simp [def_n, k_pos.le]]
  convert VermaModule.apply_hwVec_eq (HeisenbergAlgebra.chargedFockHW 𝕜 α) (some n)
  · simp only [HeisenbergAlgebra.chargedFockHW]
    aesop
  · simp only [HeisenbergAlgebra.chargedFockHW]
    aesop

open Filter HeisenbergAlgebra in
lemma ChargedFockSpace.eventually_jgen_smul_eq_zero (α : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    ∀ᶠ k in atTop, (ιUEA 𝕜 (jgen 𝕜 k)) • v = 0 := by
  have aux : v ∈ Submodule.span (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) {vacuum 𝕜 α} := by
    simp [vacuum_cyclic 𝕜 α]
  obtain ⟨a, hav⟩ := Submodule.mem_span_singleton.mp aux
  filter_upwards [uea_eventually_commute_jgen _ a, Ioi_mem_atTop 0] with k hk k_pos
  -- `calcify`?
  rw [← hav, ← mul_smul]
  rw [show _ * a = a * _ from hk]
  rw [mul_smul]
  rw [jgen_pos_vacuum _ _ k_pos, smul_zero]

end Fock_space

end VirasoroProject
