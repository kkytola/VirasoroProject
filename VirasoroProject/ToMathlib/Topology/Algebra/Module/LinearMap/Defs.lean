/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Linear maps distribute over `finsum` — **incorporated into Mathlib**

The lemma `LinearMap.map_finsum` below has been incorporated into Mathlib in generalized
form: `map_finsum` applies to any bundled map of an `AddMonoidHomClass` (which also settles
the "generalize beyond plain linear maps" TODO that the original statement here carried).

The original statement is kept as a deprecated alias for the record; new code should use
`map_finsum` directly.
-/

@[deprecated map_finsum (since := "2026-07-12")]
theorem LinearMap.map_finsum {ι 𝕜 : Type*} [Semiring 𝕜]
    {V : Type*} [AddCommMonoid V] [Module 𝕜 V] {W : Type*} [AddCommMonoid W] [Module 𝕜 W]
    (f : V →ₗ[𝕜] W) (a : ι → V) (ha : (Function.support a).Finite) :
    f (∑ᶠ i, a i) = ∑ᶠ i, f (a i) :=
  _root_.map_finsum (f := a) f ha
