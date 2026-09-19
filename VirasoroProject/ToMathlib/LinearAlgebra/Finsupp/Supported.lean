/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Membership of `finsum`s of scaled vectors in spans
-/

lemma finsum_mem_span {ι R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) :
    ∑ᶠ i, cfs i • vs i ∈ Submodule.span R (Set.range vs) := by
  by_cases h : {i | cfs i • vs i ≠ 0}.Finite
  · rw [finsum_eq_finsetSum_of_support_subset (s := h.toFinset) _
        (fun i hi ↦ by simpa using hi)]
    exact Submodule.sum_smul_mem _ _ fun i _ ↦ Submodule.mem_span_of_mem (Set.mem_range_self i)
  · suffices junk : ∑ᶠ i, cfs i • vs i = 0 by simp [junk]
    simpa using finsum_mem_eq_zero_of_infinite (s := Set.univ) (by simpa [Function.support] using h)

lemma finsum_mem_mem_span {ι R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) (s : Set ι) :
    ∑ᶠ i ∈ s, cfs i • vs i ∈ Submodule.span R (vs '' s) := by
  rw [← finsum_set_coe_eq_finsum_mem]
  refine Submodule.span_mono ?_ (finsum_mem_span (fun i : s ↦ vs i) (fun i : s ↦ cfs i))
  rintro _ ⟨i, rfl⟩
  exact Set.mem_image_of_mem vs i.2
