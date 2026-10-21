## What changed

Proved
`CategoryTheory.FlatScalarTowerLimit.flatScalarTowerLimitSquare` with its original signature.
The earlier missing published artifact is now available. The complete module compiles
cleanly through `lcompile.py` (51.2 seconds, no errors or warnings).
The delivery changes this Lean module, its proof-plan node, and the import/elaboration
change record `coord/changes/flat-scalar-tower-limit-proof-interface.md`.

The ordinary scalar/limit maps are Mathlib's `preservesLimitNatIso`, hence exactly
`limit.post`. Flat scalar extension supplies exact left adjoints, so scalar restriction
preserves ordinary limits and termwise K-injectives. Source tower categories have
K-injective resolutions by the existing small-diagram Grothendieck theorem and the
source library's Grothendieck K-injective resolution instance.

Private proved helpers construct normalized derived comparisons by Mathlib's
K-injective derivability structure and `rightDerivedUnique`, and extend equality of
natural transformations from K-injective representatives. The construction gives the
lambda unit equation on every complex. The main proof checks the ordinary square by
limit projections, then checks the derived square by an explicit unit calculation,
precomposing and postcomposing with isomorphisms. The private `square_of_normalized`
lemma provides an abstract API for the comparison structures: its calculation uses
arbitrary abelian categories, avoiding repeated reduction of concrete sheaf-module
and chosen-limit data. The concrete theorem specializes this same calculation.
No new public declaration, statement,
definition, or axiom is introduced.

## Proved and sorry left

Closed the one original hole in
`CategoryTheory.FlatScalarTowerLimit.flatScalarTowerLimitSquare`
(node `lem-weil-pbc-flat-scalar-tower-limit-square`). Holes added: zero. Holes remaining
in the module: zero. The complete proof compiles. No split-off statements.

## No longer needed

Removed public imports of `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
and `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
Replaced public import `Sheaf.CategoryTheory.FlatRingedDiagramRestriction` by its
statement-definition module `Sheaf.CategoryTheory.FlatRingedDiagramRestrictionDefs`.
The existing comparisons and their normalization hypotheses suffice; none of these
three theorem modules is used by the proof.

Removed proof imports `Sheaf.CategoryTheory.DiagramSiteRealization`,
`Sheaf.CategoryTheory.KInjectiveExactSquareComparison`,
`Sheaf.CategoryTheory.KInjectiveTotalDerived`,
`Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`, and
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.

Removed proof dependencies on `lem-weil-pbc-diagram-site-realization`,
`prop-pur-kinjective-resolutions-exist`, `lem-weil-pbc-kinjective-total-derived`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`,
`lem-weil-pbc-kinjective-exact-square-comparison`,
`lem-trf-geometric-inverse-image-exact`,
`lem-weil-pbc-flat-ringed-diagram-restriction`, and
`lem-weil-ringed-tower-pushforward-limit-comparison`.
The former proof-dependency entries `def-weil-sheaf-of-modules-category` and
`def-pc-sheaf-restrict-scalars` remain statement dependencies;
none is withdrawn. The three corresponding obsolete top-level tool approvals
(geometric inverse-image exactness, ringed-site resolutions, and pushforward/limit
comparison) are removed; the right-adjoint limit-preservation approval is retained.

The direct-image functor need not preserve K-injectives in this proof, because the
constructed lambda normalizations hold on arbitrary complexes. The existing small
module-diagram Grothendieck theorem replaces the diagram-site detour. No claim is made
that these dependencies become unused elsewhere in the project.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was required. The planned exact-square lemma is
formulated with a strict ordinary equality and canonical homotopy-category localization
factors. Here the ordinary square is an isomorphism and the theorem supplies chosen
localization factors. A direct application of Mathlib's right-derived uniqueness
handles exactly those factors and proves a stronger normalization for the constructed
comparisons, simplifying the remaining argument.

`lem-sfb-grothendieck-k-injective` is used as a generic resolution tool from another
unit: it supplies the already-proved resolution instance for the Grothendieck source
tower categories, without replacing any step of the proper-base-change unit's route.
It needs the maintainer's normal tool-use review; no new tool approval was written.
The proper-base-change unit's statement and its three realized steps are unchanged.

The retained attempt had not compiled. Its final rewriting unfolded the concrete
sheaf and limit implementations repeatedly. The abstract categorical API and explicit
equality chains address that elaboration cost without changing public data or increasing
the compiler wall-time limit.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
