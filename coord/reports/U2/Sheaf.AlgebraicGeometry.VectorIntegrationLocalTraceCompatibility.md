## What changed

Replaced the remaining body of
`AlgebraicGeometry.Etale.vectorIntegrationLocalSheafTrace_compatible_of_baseChange`
with a Lean argument from chart comparisons, the existing affine linear trace invariance,
and the existing affine tower counit base-change theorem. Existing public statements,
definitions, public imports, normalization theorem and separately normalized-family wrapper
are unchanged. All added imports in the item are private proof imports.

The proved helper modules supply the defining comparison equations, composition of
constant-unit pullback, composition of the étale single restriction comparison, and
compatibility of the inverse Hom equivalence with `compRestriction`. Private helpers in
the item supply its unit normalization, the affine constant-object counit square, and
its application to a restricted chart prefix. The defining equations and their composition
are compiled separately after profiling showed expensive kernel conversion of the derived
functors. The general categorical algebra is proved before specializing it.
The final argument uses the intersection pullback to factor the two lifts from W; W itself
is not assumed Noetherian.

Added `Sheaf.AlgebraicGeometry.VectorIntegrationOverlapChartPrefix`, containing three explicit
comparison constructions and the remaining geometric exchange equation before the counit.
The constructions use the existing exchanges and coefficient comparisons directly. They
contain no sorry and do not select data from an unproved existence theorem.

## Proved and sorry left

The item's one original hole, in
`AlgebraicGeometry.Etale.vectorIntegrationLocalSheafTrace_compatible_of_baseChange`
(node `lem-amb-vector-integration-local-trace-compatibility`), is closed by the assembly.
The item has zero remaining sorry bodies. Its assembled proof compiled in 33.5 seconds
with profiling enabled; a clean `lcompile.py --all` then compiled all seven modules in import order
with no errors or warnings. Two helper imports were subsequently narrowed from public to
private proof imports; delivery preflight checks those final import changes.

One hole is added:
`AlgebraicGeometry.Etale.vectorIntegration_overlap_chart_prefix`
(node `lem-amb-vector-integration-overlap-chart-prefix`). This is the comparison of the
restricted inverse-frame exchange/coefficient prefixes up to the actual linear action.
It mentions no projective-line datum or counit, no alpha, no sheaf Hom equivalence, and no
descent component. The frame restriction and exchange calculation is a strict part of the
original proof, not the original conclusion under another name. Its source and proof in
words are given in the module docstring and node.

Thus this delivery is a decomposition: one upper hole closed, one geometric hole added,
net zero holes; it is not a complete proof of overlap compatibility independent of the new
obligation. All categorical restriction, affine counit and sheaf evaluation steps are proved.

## No longer needed

No original item import is removed and no module is globally pruned. Unused source proof
imports were removed from the new helper modules; their public imports only expose what
their statements need. The parent now uses the
new chart-prefix node in place of directly carrying its geometric proof Steps 1--2.
`thm-cbc-finite-torsion`, `lem-asd-etale-finite-twist-pullback`, and
`def-asd-vector-bundle-zero-section` move from the parent's direct proof dependencies into
the new geometric node's dependencies; they remain needed there. The affine counit
base-change and linear trace invariance dependencies remain directly used. No blueprint
unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The stated dependencies did not provide a single Lean comparison equation for the
restricted inverse-frame prefixes on a common smaller open. Existing
`VectorIntegrationSwapChartPrefix` is about a biproduct swap over one open and does not give
this equation. The new obligation states only that missing geometric calculation; the
already available trace invariance and counit base-change declarations do finish the rest.

## New nodes

`lem-amb-vector-integration-overlap-chart-prefix`, in
`dag/nodes/sec-smooth-purity/lem-amb-vector-integration-overlap-chart-prefix.json`, attaches
the genuine prefix calculation and its three explicit constructions to
`Sheaf.AlgebraicGeometry.VectorIntegrationOverlapChartPrefix`. Its proof follows frame
restriction, the transpose/inverse coordinate convention, exchange pasting and normalized
Tate composition. Rank zero, empty opens, zero coefficients and nonaffine opens were checked
against that argument. Searches found only topological coordinate-change lemmas, not the
algebraic compact-support comparison. No change record is necessary: no existing statement,
definition, public import, or other existing module is changed.

`lem-amb-ordinary-finite-unit-pullback-hom` and
`lem-amb-ordinary-finite-unit-pullback-comp` attach the fully proved constant-object
comparison equation and its composition law, in the modules
`OrdinaryFiniteUnitPullbackHom` and `OrdinaryFiniteUnitPullbackComp`. The latter uses
source `leftDerivedUpperStarComp_hom_app_singleFunctor` and
`upperStarConstantSheafIso_comp`; neither node has a hole.

`lem-amb-etale-single-restriction-factors` and
`lem-amb-etale-single-restriction-comp` attach the fully proved factorization and
composition equations of `etaleSingleRestrictionIso`, in `EtaleSingleRestrictionFactors`
and `EtaleSingleRestrictionComp`. The composition proof applies the source
`upperStarIsoLocalizationRestriction_comp` and the degree-zero derived compositor formula.

`lem-amb-etale-degree-zero-hom-restriction` attaches the fully proved compatibility of
the inverse Hom correspondence with `compRestriction`, in `EtaleDegreeZeroHomRestriction`.
It combines the preceding comparison square with naturality and cancellation of the
specified isomorphisms. These five categorical helper nodes add no sorry.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
