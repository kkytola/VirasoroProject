/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Auxiliary lemmas about sums over finite supports

Lemmas about `Finset.sum` and `finsum` interacting with `Function.support`, candidates for
upstreaming to Mathlib. The lemma `finsum_add_finsum_compl` is used in the bosonic Sugawara
construction (`VirasoroProject.Sugawara`).

NOTE (naming): Mathlib naming around reindexed and split sums is inconsistent, compare e.g.
`Equiv.tsum_eq` with `finprod_comp_equiv`. Similarly, should `finsum_add_distrib`,
`finsum_sub_distrib`, `finsum_neg_distrib` just be `finsum_add`, `finsum_sub`, `finsum_neg`?
Compare with `tsum_add`, `tsum_sub`, `tsum_neg` (and `finsum_smul'`, `smul_finsum'`).
-/

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
  rw [← finsum_mem_univ, ← Set.union_compl_self I]
  refine finsum_mem_union' disjoint_compl_right ?_ ?_
  · exact hf.subset Set.inter_subset_right
  · exact hf.subset Set.inter_subset_right

end
