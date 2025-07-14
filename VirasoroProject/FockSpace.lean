import Mathlib
import VirasoroProject.Commutator
import VirasoroProject.VermaModule
import VirasoroProject.HeisenbergAlgebra

namespace VirasoroProject



section Fock_space

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

/-- The indexed collection of Heisenberg (associative) algebra generators
of nonnegative index (K, J₀, J₁, J₂, ...) together with the scalars by which
they act on the vacuum of the charged Fock space of charge α. -/
noncomputable def HeisenbergAlgebra.chargedFockHW (α : 𝕜) (i : Option ℕ) :
    𝓤 𝕜 (HeisenbergAlgebra 𝕜) × 𝕜 := match i with
  | none => ⟨UniversalEnvelopingAlgebra.ι 𝕜 (kgen 𝕜), 1⟩
  | some 0 => ⟨UniversalEnvelopingAlgebra.ι 𝕜 (jgen 𝕜 0), α⟩
  | some k => ⟨UniversalEnvelopingAlgebra.ι 𝕜 (jgen 𝕜 k), 0⟩

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
    (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.kgen 𝕜)) • vacuum 𝕜 α = vacuum 𝕜 α := by
  convert VermaModule.apply_hwVec_eq (HeisenbergAlgebra.chargedFockHW 𝕜 α) none
  simp [HeisenbergAlgebra.chargedFockHW]
  rfl

/-- `K • v = v` for all `v` in `ChargedFockSpace 𝕜 α` -/
@[simp] lemma ChargedFockSpace.kgen_smul (α : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.kgen 𝕜)) • v = v := by
  simpa using UniversalEnvelopingAlgebra.smul_eq_of_cyclic_of_forall_lie_eq_zero 𝕜
    (HeisenbergAlgebra 𝕜) (Z := .kgen 𝕜) (ζ := 1) (HeisenbergAlgebra.lie_kgen _)
    (vacuum_cyclic 𝕜 α) (by simpa only [map_one, one_smul] using kgen_vacuum 𝕜 α) v

/-- `J₀ • vacuum(α) = α • vacuum(α)` -/
lemma ChargedFockSpace.jgen_zero_vacuum (α : 𝕜) :
    (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.jgen 𝕜 0)) • vacuum 𝕜 α
      = α • vacuum 𝕜 α :=
  VermaModule.apply_hwVec_eq (HeisenbergAlgebra.chargedFockHW 𝕜 α) (some 0)

/-- `J₀ • v = α • v` for all `v` in `ChargedFockSpace 𝕜 α` -/
@[simp] lemma ChargedFockSpace.jgen_zero_smul (α : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.jgen 𝕜 0)) • v = α • v := by
  exact UniversalEnvelopingAlgebra.smul_eq_of_cyclic_of_forall_lie_eq_zero 𝕜
    (HeisenbergAlgebra 𝕜) (Z := .jgen 𝕜 0) (ζ := α) (HeisenbergAlgebra.lie_jgen_zero _)
    (vacuum_cyclic 𝕜 α) (jgen_zero_vacuum 𝕜 α) v

/-- `Jₖ • vacuum(α) = 0` for `k > 0` -/
lemma ChargedFockSpace.jgen_pos_vacuum (α : 𝕜) {k : ℤ} (k_pos : 0 < k) :
    (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.jgen 𝕜 k)) • vacuum 𝕜 α = 0 := by
  set n := Int.toNat k with def_n
  rw [← show (n : ℤ) = k by simp [def_n, k_pos.le]]
  convert VermaModule.apply_hwVec_eq (HeisenbergAlgebra.chargedFockHW 𝕜 α) (some n)
  · simp only [HeisenbergAlgebra.chargedFockHW]
    aesop
  · simp only [HeisenbergAlgebra.chargedFockHW]
    aesop

lemma HeisenbergAlgebra.uea_eventually_commute_jgen (a : 𝓤 𝕜 (HeisenbergAlgebra 𝕜)) :
    ∀ᶠ k in Filter.atTop,
      Commute (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.jgen 𝕜 k)) a := by
  apply UniversalEnvelopingAlgebra.induction 𝕜 _
    (C := fun a' ↦ ∀ᶠ k in Filter.atTop,
          Commute (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.jgen 𝕜 k)) a')
  · intro r
    filter_upwards [Filter.Ioi_mem_atTop 0] with k k_pos
    exact (Algebra.commutes r _).symm
  · let whole := Submodule.span 𝕜 (Set.range (HeisenbergAlgebra.basisJK 𝕜))
    suffices ∀ X ∈ whole, ∀ᶠ k in Filter.atTop,
        Commute (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.jgen 𝕜 k))
                (UniversalEnvelopingAlgebra.ι 𝕜 X) from
      fun X ↦ this X (by simp [whole])
    apply Submodule.span_induction
    · intro Z ⟨i, hiZ⟩
      match i with
      | none =>
        simp only [← hiZ, basisJK_none]
        filter_upwards [Filter.Ioi_mem_atTop 0] with k k_pos
        exact (UniversalEnvelopingAlgebra.central_of_forall_lie_eq_zero 𝕜 (HeisenbergAlgebra 𝕜)
                (congrFun rfl) ((UniversalEnvelopingAlgebra.ι 𝕜) (jgen 𝕜 k))).symm
      | some l =>
        simp only [← hiZ, basisJK_some]
        filter_upwards [Filter.Ioi_mem_atTop |l|] with k hk
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

lemma ChargedFockSpace.eventually_jgen_smul_eq_zero (α : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    ∀ᶠ k in Filter.atTop, (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.jgen 𝕜 k)) • v = 0 := by
  have aux : v ∈ Submodule.span (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) {vacuum 𝕜 α} := by
    simp [ChargedFockSpace.vacuum_cyclic 𝕜 α]
  obtain ⟨a, hav⟩ := Submodule.mem_span_singleton.mp aux
  have bar : ∀ᶠ k in Filter.atTop, 0 < k :=
    Filter.Tendsto.eventually_gt_atTop (fun ⦃_⦄ a ↦ a) 0
  filter_upwards [HeisenbergAlgebra.uea_eventually_commute_jgen _ a,
                  Filter.Ioi_mem_atTop 0] with k hk k_pos
  -- `calcify`?
  rw [← hav, ← mul_smul]
  rw [show _ * a = a * _ from hk]
  rw [mul_smul]
  rw [jgen_pos_vacuum _ _ k_pos, smul_zero]

end Fock_space

end VirasoroProject
