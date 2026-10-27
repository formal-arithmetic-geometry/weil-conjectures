## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientComparison_affineCech_vanishing` with
its original statement, coefficient universes, hypotheses and public imports.
The proof uses a simultaneous affine étale presentation, continuity of comparison
sections, and injective module-presheaf Čech cocycle lifting. It proves the finite
filtered-colimit passage explicitly: represent finitely many components at one
stage, make their differential zero at one later stage, take a stage primitive,
and compare that primitive with the original cochain.

Added `Sheaf.AlgebraicGeometry.CoefficientAffineCechSystem` and
`Sheaf.AlgebraicGeometry.CoefficientAffineCechPresentation`. The presentation
structure records every index-map identity, including repeated factors. Its
existence theorem is proved: the existing finite covering-presentation argument
works without its unused affine-ambient hypothesis, and the proved canonical
nerve construction supplies scheme limits of intersections. Unique product
isomorphisms normalize these intersections to the prescribed `SiteCechComplex`;
AsSmall transports both the site and the index universe. Existing library files
other than the assigned item are unchanged.

The proof helpers use a private declaration scope, keeping the new presentation
data out of the public interface. The returned packet used an explicit
`public theorem` modifier, which the landing declaration scanner did not index.
The repair restores the original plain `theorem` form inside an exposed public
section, preserving the theorem name and its complete signature. The scanner now
finds the original declaration. Remote compilation of the repaired item passed
in 44.4 s, and the unchanged direct consumer
`CoefficientComparisonAffineSections` compiled against it in 9.6 s. The temporary
consumer copy was removed before delivery.

The private constant-scalar equivalence and comparison isomorphism reproduce the
proved scalar argument of `CoefficientComparisonFixedPullback`; that module's
public theorem is about scheme base-change pullbacks and is not the comparison
isomorphism needed here. All new imports of the item are private proof imports.
The item node and the new geometric node record the implemented route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.coefficientComparison_affineCech_vanishing`
(`lem-pe-coefficient-comparison-affine-cech`).

Also proved
`AlgebraicGeometry.ProEtale.exists_coefficient_affine_cech_presentation`
(`lem-pe-coefficient-affine-cech-presentation`). There are zero remaining holes in
the item and zero holes added elsewhere. No obligation is split off. Remote compilation passed: the system module took
6.8 s, the geometric proof 22.4 s, and the assigned module 44.4 s, each below
the 60 s limit. The new
geometric module and all private algebraic and transport helpers contain no
`sorry`.

## No longer needed

No original imports were removed, and no module is withdrawn. The following
planned dependencies are not direct dependencies of this proof:

- `def-weil-pbc-ind-etale-algebra`,
  `lem-weil-pbc-ind-etale-stability`,
  `lem-weil-pbc-cofiltered-limit-directed-reindex`,
  `lem-weil-pbc-etale-finite-data-descent`, and
  `lem-weil-pbc-limit-affine-stage`: the geometric construction uses the proved
  affine-site relative-presentation and finite open-cover descent APIs directly;
  its index stays cofiltered and is transported by an equivalence.
- `lem-weil-pbc-ringed-site-injective-module-cech-acyclic`: the stronger proved
  injective-presheaf cocycle-lifting theorem gives actual primitives, after the
  proved sheaf-to-presheaf injectivity theorem and a finite-index universe lift.
- `lem-pe-coefficient-comparison-fixed-pullback` and
  `lem-weil-pbc-site-module-sheaf-constant-ring-equivalence`: the required scalar
  comparison is proved locally from the canonical ring map and adjunctions.
- `lem-weil-pbc-filtered-colimits-commute-finite-limits` and
  `lem-weil-pbc-filtered-colimit-abelian-groups-exact`: the finite representative
  and eventual-equality proof replaces these abstract statements. It uses the
  concrete filtered-colimit API of `Mathlib.Algebra.Category.Grp.FilteredColimits`.

These are dependency reductions for this node, not claims that the declarations
can be removed from the adopted source library or that no other target needs them.
The original `SiteCechComplex` and coefficient comparison continuity remain used.

## Where the brief, the DAG or earlier work was wrong

The existing public finite covering-presentation theorem requires `IsAffine X`,
although its proof does not use that hypothesis: the source and target objects
are already absolutely affine by pro-affine-étaleness. A private copy of that
argument removes this obstacle without changing its shared interface.

The scalar base-change theorem is not directly the natural isomorphism needed
between intrinsic comparison pullback and fixed-scalar comparison. The existing
private scalar argument proves that isomorphism here. The return's duplicate-statement messages concern proved private helpers and
are advisory; no public duplicate is introduced. No false statement or
change of target meaning was found. Empty covers, repeated indices, non-affine
ambient schemes, and the zero coefficient ring are included by the same proof.

## New nodes

`lem-pe-coefficient-affine-cech-presentation`, in
`dag/nodes/sec-proetale-coefficients/`, states the purely geometric compatible
presentation theorem. It has no coefficient ring, sheaf, injectivity, cohomological
degree or vanishing assertion. Its full proof is supplied in the new module;
it introduces no outstanding item. Its source is Stacks Tag 099U and the finite
cover descent results used by the existing proved geometric presentation APIs.
`def-pe-coefficient-affine-cech-presentation` records its explicit data structure
and tuple diagram/cone in `CoefficientAffineCechSystem`. These definitions contain
no postponed data or properties.

No change record is needed: no existing shared interface or other node is changed.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
