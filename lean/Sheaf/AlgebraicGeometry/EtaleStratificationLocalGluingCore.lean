module

public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Constructible

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A finite affine-local immersed partition admits a global immersed refinement with actual
factorization maps into its local representatives. Source: Stacks Project, Etale Cohomology,
Tag 03S0, locality reduction
(blueprint: lem-weil-pbc-etale-stratification-local-gluing-core).

Proof: Each affine chart is quasi-compact and therefore retrocompact in the quasi-separated
base. Its locally constructible strata are constructible in the base. Extend its partition by
its closed complement, realized by the reduced closed subscheme. Compose each local immersion
with the chart inclusion. Take the finite common refinement of the extended partitions using
intersections, represented by fibre products. Discard empty strata. Each remaining stratum
contains a point, and that point belongs to some chart. Refinement forces the whole stratum to
lie in one local part of that chart, rather than its complement. Replace its scheme
representative by its fibre product with this local representative. The resulting composite
immersion has the same image, by the image formula for scheme pullbacks, so constructibility,
disjointness and coverage are preserved. The second projection is the requested factorization.
If the base is empty, take the zero-stratum partition. -/
theorem exists_global_stratification_factoring_local
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (n : ℕ) (W : Fin n → X.Opens)
    (hW : ∀ a, IsAffineOpen (W a))
    (hcover : (⋃ a : Fin n, (W a : Set X)) = Set.univ)
    (T : ∀ a, LocallyClosedStratification (W a))
    (hc : ∀ a b, Topology.IsConstructible ((T a).stratum b)) :
    ∃ S : LocallyClosedStratification X,
      (∀ i, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i, ∃ (a : Fin n) (b : Fin (T a).n)
        (q : S.domain i ⟶ (T a).domain b),
        q ≫ ((T a).immersion b ≫ (W a).ι) = S.immersion i := by
  sorry

end AlgebraicGeometry.Scheme
