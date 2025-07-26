/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib
import VirasoroProject.Sugawara
import VirasoroProject.FockSpace

namespace VirasoroProject



section Fock_space_Sugawara_construction

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

section auxiliary

variable {V : Type*} [AddCommGroup V] [Module (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V]

open HeisenbergAlgebra in
private lemma commutator_lsmul_jgen_of_module_uea_heisenbergAlgebra
    (hc : ∀ (v : V), (ιUEA 𝕜 (kgen 𝕜)) • v = v) (k l : ℤ) :
    (ModuleOfModuleAlgebra.lsmul 𝕜 V (ιUEA 𝕜 (jgen 𝕜 k))).commutator
      (ModuleOfModuleAlgebra.lsmul 𝕜 V (ιUEA 𝕜 (jgen 𝕜 l)))
    = if k + l = 0 then (k : 𝕜) • 1 else 0 := by
  have key (w : V) :
      (ιUEA 𝕜 (jgen 𝕜 k)) • (ιUEA 𝕜 (jgen 𝕜 l)) • w - (ιUEA 𝕜 (jgen 𝕜 l)) • (ιUEA 𝕜 (jgen 𝕜 k)) • w
        = if k + l = 0 then ↑k • w else 0 := by
    have key := congr_arg (fun b ↦ b • w) <| (ιUEA 𝕜).map_lie (jgen 𝕜 k) (jgen 𝕜 l)
    rw [lie_jgen 𝕜 k l] at key
    by_cases hkl : k + l = 0
    · simp only [hkl, ↓reduceIte, LieHom.map_smul] at key ⊢
      convert key.symm using 1
      · simp_rw [← smul_assoc, ← sub_smul]
        rfl
      · have same :
            k • w = (algebraMap 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) ↑k • ιUEA 𝕜 (kgen 𝕜)) • w := by
          rw [smul_assoc, hc]
          simpa [map_intCast] using (Int.cast_smul_eq_zsmul (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) k w).symm
        convert same using 1
        congr 1
        exact algebra_compatible_smul (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) (↑k) (ιUEA 𝕜 (kgen 𝕜))
    · simp only [hkl, ↓reduceIte, LieHom.map_zero, zero_smul] at key ⊢
      simp_rw [← smul_assoc, ← sub_smul]
      convert key.symm using 1
  ext v
  convert key v using 1
  by_cases hkl : k + l = 0 <;> simp [hkl, Int.cast_smul_eq_zsmul]

open HeisenbergAlgebra Filter in
-- TODO: Generalize to `kgen` acting as `κ • 1`, maybe.
/-- **The basic bosonic Sugawara representation of Virasoro algebra (c=1)**:
On a module over the universal enveloping algebra of the Heisenberg algebra in which the Heisenberg
algebra acts locally truncatedly (and the central element `k` acts as `1`), we get a representation
of the Virasoro algebra with central charge `c = 1` by the Sugawara construction. -/
noncomputable def sugawaraRepresentation_of_module_uea_heisenbergAlgebra
    (htrunc : ∀ (v : V), ∀ᶠ (k : ℤ) in atTop, ιUEA 𝕜 (jgen 𝕜 k) • v = 0)
    (hc : ∀ (v : V), (ιUEA 𝕜 (kgen 𝕜)) • v = v) :
    LieAlgebra.Representation 𝕜 𝕜 (VirasoroAlgebra 𝕜)
      (ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V) :=
  let heiOper (k : ℤ) :
      ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V
        →ₗ[𝕜] ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V :=
    ModuleOfModuleAlgebra.lsmul 𝕜 V (ιUEA 𝕜 (jgen 𝕜 k))
  sugawaraRepresentation (heiOper := heiOper)
    (fun v ↦ htrunc ((ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V) v))
    (commutator_lsmul_jgen_of_module_uea_heisenbergAlgebra 𝕜 hc)

open HeisenbergAlgebra Filter in
lemma sugawaraRepresentation_of_module_uea_heisenbergAlgebra_lgen_apply
    (htrunc : ∀ (v : V), ∀ᶠ (k : ℤ) in atTop, ιUEA 𝕜 (jgen 𝕜 k) • v = 0)
    (hc : ∀ (v : V), ιUEA 𝕜 (kgen 𝕜) • v = v)
    (n : ℤ) (v : ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V) :
    sugawaraRepresentation_of_module_uea_heisenbergAlgebra 𝕜 htrunc hc (.lgen 𝕜 n) v =
      (2 : 𝕜)⁻¹ • ModuleOfModuleAlgebra.mkAddHom 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V (
          ((∑ᶠ k ≥ 0, ιUEA 𝕜 (jgen 𝕜 (n-k)) • ιUEA 𝕜 (jgen 𝕜 k)
                      • ModuleOfModuleAlgebra.unMkAddHom 𝕜 _ V v)
          + (∑ᶠ k < 0, ιUEA 𝕜 (jgen 𝕜 k) • ιUEA 𝕜 (jgen 𝕜 (n-k))
                      • ModuleOfModuleAlgebra.unMkAddHom 𝕜 _ V v))) := by
  apply sugawaraRepresentation_lgen_apply _
    ((fun v ↦ htrunc ((ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V) v)))
    (commutator_lsmul_jgen_of_module_uea_heisenbergAlgebra 𝕜 hc)

end auxiliary


namespace ChargedFockSpace

/-- **Virasoro algebra representation on Fock space by basic bosonic Sugawara construction (c=1)**:
-/
noncomputable def sugawaraRepresentation (α : 𝕜) :
    LieAlgebra.Representation 𝕜 𝕜 (VirasoroAlgebra 𝕜) (ChargedFockSpace 𝕜 α) :=
  sugawaraRepresentation_of_module_uea_heisenbergAlgebra 𝕜 (V := ChargedFockSpace 𝕜 α)
      (fun _ ↦ eventually_jgen_smul_eq_zero ..) (fun _ ↦ ChargedFockSpace.kgen_smul ..)

open HeisenbergAlgebra in
/-- The formula for the action of the Virasoro generators in the (basic) Sugawara
representation on the charged Fock space. -/
lemma sugawaraRepresentation_lgen_apply
    (α : 𝕜) (n : ℤ) (v : ChargedFockSpace 𝕜 α) :
    ChargedFockSpace.sugawaraRepresentation 𝕜 α (.lgen 𝕜 n) v =
      (2 : 𝕜)⁻¹
        • ((∑ᶠ k ≥ 0, ιUEA 𝕜 (jgen 𝕜 (n-k)) • ιUEA 𝕜 (jgen 𝕜 k) • v)
          + (∑ᶠ k < 0, ιUEA 𝕜 (jgen 𝕜 k) • ιUEA 𝕜 (jgen 𝕜 (n-k)) • v)) := by
  apply sugawaraRepresentation_of_module_uea_heisenbergAlgebra_lgen_apply

open HeisenbergAlgebra in
lemma sugawaraRepresentation_lgen_apply_vacuum (α : 𝕜) (n : ℤ) :
    ChargedFockSpace.sugawaraRepresentation 𝕜 α (.lgen 𝕜 n) (vacuum 𝕜 α) =
      (2 : 𝕜)⁻¹
        • ((ιUEA 𝕜 (jgen 𝕜 n) • ιUEA 𝕜 (jgen 𝕜 0) • (vacuum 𝕜 α))
          + (∑ᶠ k < 0, ιUEA 𝕜 (jgen 𝕜 k) • ιUEA 𝕜 (jgen 𝕜 (n-k)) • (vacuum 𝕜 α))) := by
  simp only [sugawaraRepresentation_lgen_apply, ge_iff_le]
  congr 1
  simp only [add_left_inj]
  convert @finsum_eq_single (ChargedFockSpace 𝕜 α) ℤ _ _ 0 ?_
  · simp
  · intro k k_ne_zero
    by_cases k_nn : 0 ≤ k
    · simp only [k_nn, finsum_true]
      rw [jgen_pos_vacuum 𝕜 α (show 0 < k by grind), smul_zero]
    · simp [k_nn]

open HeisenbergAlgebra in
lemma sugawaraRepresentation_lgen_nonneg_apply_vacuum
    (α : 𝕜) {n : ℤ} (n_nn : 0 ≤ n) :
    ChargedFockSpace.sugawaraRepresentation 𝕜 α (.lgen 𝕜 n) (vacuum 𝕜 α) =
      (2 : 𝕜)⁻¹ • ιUEA 𝕜 (jgen 𝕜 n) • ιUEA 𝕜 (jgen 𝕜 0) • (vacuum 𝕜 α) := by
  simp only [sugawaraRepresentation_lgen_apply_vacuum, smul_add]
  convert add_zero ..
  convert smul_zero ..
  · convert finsum_zero with k
    by_cases k_neg : k < 0
    · simp only [k_neg, finsum_true]
      rw [jgen_pos_vacuum 𝕜 α (show 0 < n - k by linarith), smul_zero]
    · simp [k_neg]

/-- The vacuum in the Fock space of charge α has L₀-eigenvalue α²/2. -/
lemma sugawaraRepresentation_lgen_zero_apply_vacuum (α : 𝕜) :
    sugawaraRepresentation 𝕜 α (.lgen 𝕜 0) (vacuum 𝕜 α) =
      (α^2 / 2) • (vacuum 𝕜 α) := by
  rw [sugawaraRepresentation_lgen_nonneg_apply_vacuum 𝕜 α le_rfl]
  simp only [jgen_zero_smul, ← smul_assoc, smul_eq_mul]
  grind

/-- The vacuum in the Fock space of charge α is annihilated by Lₙ for n > 0. -/
lemma sugawaraRepresentation_lgen_pos_apply_vacuum (α : 𝕜)
    {n : ℤ} (n_pos : 0 < n) :
    sugawaraRepresentation 𝕜 α (.lgen 𝕜 n) (vacuum 𝕜 α) = 0 := by
  rw [sugawaraRepresentation_lgen_nonneg_apply_vacuum 𝕜 α n_pos.le]
  convert smul_zero ..
  simp only [jgen_zero_smul]
  rw [smul_comm, jgen_pos_vacuum 𝕜 α n_pos, smul_zero]

end ChargedFockSpace

end Fock_space_Sugawara_construction

end VirasoroProject
