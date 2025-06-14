import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Module.LinearMap.Defs
import VirasoroProject.ToMathlib.Topology.Algebra.BigOperators.FinProd

section

-- NOTE: Should be in Mathlib! But Generalize to semilinear maps first...
lemma LinearMap.map_finsum {ι 𝕜 : Type*} [Semiring 𝕜]
    {V : Type*} [AddCommMonoid V] [Module 𝕜 V] {W : Type*} [AddCommMonoid W] [Module 𝕜 W]
    (f : V →ₗ[𝕜] W) (a : ι → V) (ha : (Function.support a).Finite) :
    f (∑ᶠ i, a i) = ∑ᶠ i, f (a i) := by
  rw [finsum_eq_sum _ ha, map_sum, ← finsum_eq_sum_of_support_subset (fun i ↦ f (a i))]
  intro i hi
  simp only [Function.mem_support, ne_eq, Set.Finite.coe_toFinset] at hi ⊢
  intro con
  simp [con] at hi

-- NOTE: Mathlib naming is inconsistent:
--#check Equiv.tsum_eq
--#check finsum_comp_equiv

-- Should these just be `finsum_add` and `finsum_sub` and `finsum_neg`?
-- Compare with `tsum_add` and `tsum_sub` and `tsum_neg` (and `finsum_smul` and `smul_finsum`).
--#check finsum_add_distrib
--#check finsum_sub_distrib
--#check finsum_neg_distrib
--#check tsum_add
--#check tsum_sub
--#check tsum_neg
--#check smul_finsum
--#check finsum_smul

end
