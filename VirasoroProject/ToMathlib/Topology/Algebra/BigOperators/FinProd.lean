import Mathlib.Algebra.BigOperators.Finprod

section

lemma Finset.sum_eq_sum_support {ι R : Type*} [AddCommMonoid R] {s : Finset ι} {f : ι → R}
    (hf : (Function.support f).Finite) (hs : Function.support f ⊆ (s : Set ι)) :
    ∑ i ∈ s, f i = ∑ i ∈ hf.toFinset, f i := by
  simpa [← finsum_eq_sum_of_support_subset f hs] using finsum_eq_sum f hf

lemma Finset.sum_eq_sum_of_support_subset_of_support_subset {ι R : Type*} [AddCommMonoid R]
    {s₁ s₂ : Finset ι} {f : ι → R} (hf : (Function.support f).Finite)
    (hs₁ : Function.support f ⊆ (s₁ : Set ι)) (hs₂ : Function.support f ⊆ (s₂ : Set ι)) :
    (∑ i ∈ s₁, f i) = (∑ i ∈ s₂, f i) := by
  rw [sum_eq_sum_support hf hs₁, sum_eq_sum_support hf hs₂]

lemma finsum_add_finsum_compl {V : Type*} [AddCommMonoid V] {ι : Type*} (I : Set ι) (f : ι → V)
    (hf : (Function.support f).Finite) :
    ∑ᶠ i, f i = (∑ᶠ i ∈ I, f i) + (∑ᶠ i ∈ Iᶜ, f i) := by
  -- There must be a better way, but I didn't find the right API lemmas.
  classical
  simp_rw [finsum_def]
  simp only [hf, ↓reduceDIte]
  have aux : hf.toFinset
              = (hf.toFinset.filter (fun i ↦ i ∈ I)) ∪ (hf.toFinset.filter (fun i ↦ ¬ i ∈ I)) := by
    rw [Finset.filter_union_filter_neg_eq]
  have key := @Finset.sum_union ι V
            (hf.toFinset.filter (fun i ↦ i ∈ I)) (hf.toFinset.filter (fun i ↦ ¬ i ∈ I))
            _ f _ (Finset.disjoint_filter_filter_neg hf.toFinset hf.toFinset (· ∈ I))
  rw [← aux] at key
  have obs (J : Set ι) (i) (hi : i ∈ {i ∈ hf.toFinset | i ∈ J}) : ∑ᶠ (_ : i ∈ J), f i = f i := by
    rw [finsum_eq_indicator_apply]
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support] at hi
    simp [hi.2]
  have obs_f (i) (J : Set ι) (hifI : i ∉ hf.toFinset) : ∑ᶠ (_ : i ∈ J), f i = 0 := by
    by_cases hiI : i ∈ J
    · simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support, not_and] at hifI
      simpa [hiI] using hifI
    · simp [hiI]
  have obs_f_nonzero {i} (J : Set ι) : ∑ᶠ (_ : i ∈ J), f i ≠ 0 → (i ∈ J ∧ i ∈ hf.toFinset) := by
    contrapose!
    intro h
    by_cases hiJ : i ∈ J
    · exact obs_f _ _ (h hiJ)
    · simp [hiJ]
  convert key
  · rw [dite_cond_eq_true]
    · have obs_Ic (i) (hiIc : i ∉ I) : ∑ᶠ (_ : i ∈ I), f i = 0 := by simp [hiIc]
      rw [Finset.sum_eq_sum_of_support_subset_of_support_subset
              (s₂ := (hf.toFinset.filter (fun i ↦ i ∈ I)))]
      · apply Finset.sum_congr rfl (obs I)
      · apply hf.subset
        simp only [Function.support_subset_iff, Function.mem_support]
        intro i hi
        by_cases hiI : i ∈ I
        · simpa using (obs_f_nonzero _ hi).2
        · simp [hiI] at hi
      · intro i hi
        simpa using Function.mem_support.mp hi
      · intro i hi
        have := obs_f_nonzero _ hi
        simpa [this.1] using this.2
      · simp only [eq_iff_iff, iff_true]
        apply hf.subset
        intro i hi
        have := obs_f_nonzero _ hi
        simpa [this.1] using this.2
  · rw [dite_cond_eq_true]
    · rw [Finset.sum_eq_sum_of_support_subset_of_support_subset
              (s₂ := (hf.toFinset.filter (fun i ↦ i ∈ Iᶜ)))]
      · convert Finset.sum_congr rfl (obs Iᶜ)
      · apply hf.subset
        simp only [Function.support_subset_iff, Function.mem_support]
        intro i hi
        by_cases hiI : i ∈ Iᶜ
        · simpa using (obs_f_nonzero Iᶜ hi).2
        · simp only [Set.mem_compl_iff, Decidable.not_not] at hiI
          simp [hiI] at hi
      · intro i hi
        simpa using Function.mem_support.mp hi
      · intro i hi
        have := obs_f_nonzero Iᶜ hi
        simpa using ⟨by simpa using this.2, by simpa using this.1⟩
      · simp only [eq_iff_iff, iff_true]
        apply hf.subset
        intro i hi
        have := obs_f_nonzero Iᶜ hi
        simpa [this.1] using this.2

end
