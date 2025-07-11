import Mathlib
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
lemma ChargedFockSpace.kgen_smul (α : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.kgen 𝕜)) • v = v := by
  simpa using UniversalEnvelopingAlgebra.smul_eq_of_cyclic_of_forall_lie_eq_zero 𝕜
    (HeisenbergAlgebra 𝕜) (Z := .kgen 𝕜) (ζ := 1) (HeisenbergAlgebra.kgen_bracket _)
    (vacuum_cyclic 𝕜 α) (by simpa only [map_one, one_smul] using kgen_vacuum 𝕜 α) v

/-- `J₀ • vacuum(α) = α • vacuum(α)` -/
lemma ChargedFockSpace.jgen_zero_vacuum (α : 𝕜) :
    (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.jgen 𝕜 0)) • vacuum 𝕜 α
      = (algebraMap 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) α) • vacuum 𝕜 α :=
  VermaModule.apply_hwVec_eq (HeisenbergAlgebra.chargedFockHW 𝕜 α) (some 0)

/-- `J₀ • v = α • v` for all `v` in `ChargedFockSpace 𝕜 α` -/
lemma ChargedFockSpace.jgen_zero_smul (α : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    (UniversalEnvelopingAlgebra.ι 𝕜 (HeisenbergAlgebra.jgen 𝕜 0)) • v
      = algebraMap 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) α • v := by
  exact UniversalEnvelopingAlgebra.smul_eq_of_cyclic_of_forall_lie_eq_zero 𝕜
    (HeisenbergAlgebra 𝕜) (Z := .jgen 𝕜 0) (ζ := α) (HeisenbergAlgebra.jgen_zero_bracket _)
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

end Fock_space

end VirasoroProject
