/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Summability in a discrete group is eventual vanishing

Candidate for Mathlib: in a discrete topological additive group, a family is summable
iff all but finitely many of its terms vanish.

Upstream status (checked against Mathlib `052559c`, 2026-07): both directions have been
incorporated (`Summable.hasFiniteSupport_of_discreteTopology` and
`summable_of_hasFiniteSupport`); only this packaged iff — in the `Filter.cofinite`
phrasing convenient for `filter_upwards` — is not in Mathlib. Compared to the original
version of this lemma, the proof is now a two-liner from the incorporated halves, and a
spurious `[DecidableEq ι]` hypothesis is gone.
-/

open Filter

lemma DiscreteTopology.summable_iff_eventually_zero
    {E : Type*} [AddCommGroup E] [TopologicalSpace E] [DiscreteTopology E]
    {ι : Type*} (f : ι → E) :
    Summable f ↔ ∀ᶠ n in cofinite, f n = 0 := by
  rw [eventually_cofinite]
  exact ⟨fun h ↦ h.hasFiniteSupport_of_discreteTopology, fun h ↦ summable_of_hasFiniteSupport h⟩
