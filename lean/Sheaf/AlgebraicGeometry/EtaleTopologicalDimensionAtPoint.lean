module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Etale morphisms preserve topological dimension at a point

Source: Stacks Project, Descent, Tag 04N4, lemma-dimension-at-point-local
(blueprint: lem-sfb-etale-topological-dimension-at-point).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An etale morphism preserves the minimum of the topological Krull dimensions of
open neighbourhoods, with infinite dimensions allowed.
Source: Stacks Project, Descent, Tag 04N4, lemma-dimension-at-point-local
(blueprint: lem-sfb-etale-topological-dimension-at-point).

Proof:
1. By sobriety of schemes (`lem-sc-scheme-sober`), chains of irreducible closed
   subsets correspond to finite strict specialization chains. Their length supremum
   is topological Krull dimension (`def-kun-topological-krull-dimension`).
2. Etale fibres are discrete (`lem-weil-pbc-etale-fibre-discrete-separable-points`),
   and the scheme fibre is homeomorphic to the subspace fibre (`def-pc-scheme-fibre`).
   Thus comparable distinct source points cannot have the same image. Continuity
   sends every strict specialization chain to a strict chain in the target.
3. For each open neighbourhood B of e(x), its inverse image A contains x, and
   step 2 gives dim A <= dim B. Taking neighbourhood infima
   (`def-kun-topological-dimension-at-point`) gives dim_x U <= dim_e(x) V.
4. Etale maps are flat and locally of finite presentation (`def-weil-etale-morphism`),
   hence open (`lem-weil-pbc-flat-lfp-open`). For any open neighbourhood A of x,
   B = e(A) is an open neighbourhood of e(x), and A maps onto B.
5. Lift a finite strict specialization chain in B starting with a point of A over
   its most specialized point. The stalk map is flat and local
   (`def-weil-flat-morphism`). Generalizations are the images of primes of the local
   ring (`lem-weil-pbc-spec-local-ring-canonical-morphism`). Flat going down
   (`lem-sc-flat-going-down`) successively lifts the primes. The lifted points stay
   in A because opens contain generalizations; they are distinct because their
   images are distinct. Thus dim B <= dim A.
6. Take the infimum over A to get dim_e(x) V <= dim_x U and use antisymmetry.
   All dimension comparisons use suprema of finite chain lengths and neighbourhood
   infima, so they include infinity without choosing an infinite chain. -/
theorem Scheme.Hom.topologicalKrullDimAt_eq_of_etale
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] (x : U) :
    topologicalKrullDimAt x = topologicalKrullDimAt (e x) := by
  sorry

end AlgebraicGeometry
