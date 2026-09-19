/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.Order

/-!
# Convergence in a discrete space is eventual equality
-/

open Filter
open scoped Topology

lemma DiscreteTopology.tendsto_nhds_iff_eventually_eq
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {ι : Type*} {F : Filter ι}
    (f : ι → X) (x : X) :
    F.Tendsto f (𝓝 x) ↔ F.Eventually (fun i ↦ f i = x) := by
  rw [nhds_discrete, tendsto_pure]
