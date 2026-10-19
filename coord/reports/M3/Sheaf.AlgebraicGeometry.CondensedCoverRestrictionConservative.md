## What changed
Proved `AlgebraicGeometry.ProEtale.condensed_cover_restriction_conservative` from the
published pro-etale sheaf conservativity theorem, coefficient transport along
`condensedPullbackHom`, and the exact derived homology comparison. A proved private
helper detects isomorphisms of module morphisms by forgetting their actions.
The theorem signature and all coefficient constructions are unchanged. Updated the
DAG proof and proof dependencies to this shorter route.

Change record: `coord/changes/M3-condensed-cover-conservativity-imports.md`.
The assigned module compiles in 4.0 seconds; both direct consumers compile unchanged
against its pruned interface (5.1 and 11.6 seconds).

## Proved and sorry left
Closed the one original hole:
`AlgebraicGeometry.ProEtale.condensed_cover_restriction_conservative`
(`lem-zl-condensed-cover-restriction-conservative`). No holes added or split off.
There are no sorries in the delivered Lean file. The two unproved intermediate
modules of the earlier, undelivered attempt are unnecessary and retained only in
`scratchpad/earlier-attempt`, outside the delivery.

## No longer needed
Removed imports `Sheaf.CategoryTheory.RingedSiteModules`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
`Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`,
`Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`,
`Mathlib.CategoryTheory.Sites.LocalProperties`,
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
The defining imports already provide the module-object and coefficient interfaces;
the existing source lemmas directly supply localization, cover conservativity and
derived homology comparison. The independent slice-site, constant-coefficient and
site-properties proofs are unused.

Removed proof dependencies `lem-weil-proetale-weakly-etale-localization`,
`lem-sfb-proetale-object-inverse-image-restriction`,
`def-weil-pbc-proetale-operations`, `det-pe-topos-functoriality-site`,
`def-weil-sheaf-of-modules-category`, and `def-weil-abstract-derived-category`.
The remaining general sheaf criterion and exact cohomology criterion are provided
by already-proved specializations in the source library. Withdrew both obsolete
tool-use approvals from this node because their declarations are unused.
The earlier attempt's proposed homology-reflection and homology-zero modules and
nodes were never landed and are not delivered.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt's claim that two new unproved homology theorems were needed
was incorrect: the source library already proves pro-etale sheaf conservativity
for arbitrary value categories, the weakly etale localization comparison and the
natural homology comparison for exact derived functors. Its assigned theorem
also remained sorry, which the initial dry run correctly refused. This delivery
uses those existing results and proves both claimed conclusions directly.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
