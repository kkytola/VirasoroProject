/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Scalar actions on discrete spaces are continuous

Candidate for Mathlib: on a discrete topological space, any scalar action is
(constantly) continuous. Stated as a `lemma` rather than an `instance` pending
upstreaming (Mathlib would want to decide on instance priority).

Upstream status (checked against Mathlib `052559c`, 2026-07): not in Mathlib
(no `DiscreteTopology`-based `ContinuousConstSMul` instance exists).
-/

lemma continuousConstSMul_of_discreteTopology (𝕜 X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] [SMul 𝕜 X] :
    ContinuousConstSMul 𝕜 X :=
  ⟨fun _ ↦ continuous_of_discreteTopology⟩
