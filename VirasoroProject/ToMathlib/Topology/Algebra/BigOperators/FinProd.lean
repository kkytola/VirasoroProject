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

end
