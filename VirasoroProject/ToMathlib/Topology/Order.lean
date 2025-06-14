import Mathlib.Topology.Order

section

open Filter
open scoped Topology

lemma DiscreteTopology.tendsto_nhds_iff_eventually_eq
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {ι : Type*} {F : Filter ι}
    (f : ι → X) (x : X) :
    F.Tendsto f (𝓝 x) ↔ F.Eventually (fun i ↦ f i = x) := by
  constructor <;>
  · intro h ; simp_all

end
