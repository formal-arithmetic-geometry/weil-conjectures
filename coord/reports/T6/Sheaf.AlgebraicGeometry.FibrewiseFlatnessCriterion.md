## What changed

Proved `AlgebraicGeometry.Scheme.Hom.flatAt_and_base_flatAt_of_fiber_flatAt` in
`Sheaf.AlgebraicGeometry.FibrewiseFlatnessCriterion`, preserving its signature,
public imports, and existing docstrings. Five proved private helpers supply the
finite-presentation stalk model, local-ring criterion, arbitrary-point fibre
quotient, commuting stalk square for locally ringed spaces, and flatness transport through quotient
equivalences.
Added proof imports of `Sheaf.RingTheory.FiniteTypeLocalClosedFibreApproximation`
and `Mathlib.RingTheory.TensorProduct.Quotient`. Updated the item's proof plan,
proof dependencies and proof origin to match the Lean proof.

The finite-presentation stalk model generalizes the construction in
`WeilConjectures.AlgebraicGeometry.FinitePresentationStalkLocalizationModel`
from affine schemes to affine open charts. The finite-type stalk property is
Mathlib's `LocallyOfFiniteType.stalkMap`. The local argument applies the existing
`Module.flat_of_flat_closedFiber` to the surjective finite-presentation
approximation, then faithful flatness proves its injectivity. Quotient actions
and all point identifications are checked explicitly in Lean.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Hom.flatAt_and_base_flatAt_of_fiber_flatAt`
(node `lem-sfb-fibrewise-flatness-criterion`). No holes remain in the delivered
module; no holes or new statements with sorry were added elsewhere; zero split off.

The proof uses the existing theorem
`Algebra.exists_finitePresentation_local_approximation_closedFibre`
(node `lem-sfb-finite-type-local-closed-fibre-approximation`), whose proof has now
landed. The criterion is proved from the assigned existing declarations. Its
transitive axiom closure still includes `sorryAx` through existing dependencies;
this delivery introduces no holes. All new private helpers are proved.

Validation: the repaired file compiles through lcompile.py in 7.2 seconds.
An explicit `#print axioms` check confirms the existing transitive `sorryAx`
dependency, alongside `propext`, `Classical.choice` and `Quot.sound`; the temporary
check commands were removed. Delivery preflight checks the unchanged signature. No source-library
file, public interface, target statement, or consumer was changed.

## No longer needed

The proof does not use `lem-sfb-fibre-flatness-compatible-stalk-data` or
`lem-sfb-flat-closed-fibre-approximation-rigidity`. Their constituent arguments
are proved by private helpers from existing declarations, so neither of these
unstated combined dependency nodes needs a new Lean module for this proof.
They remain in the DAG; no module is withdrawn or deleted.

Removed redundant proof imports:
`Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.AlgebraicGeometry.OpenImmersion`,
`Mathlib.RingTheory.FiniteStability`,
`Mathlib.RingTheory.EssentialFiniteness`,
`Mathlib.RingTheory.FiniteType`, and
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`.
All six existing public imports are preserved.
The direct localization-preservation lemma replaces the original docstring's
explicit tensor-product presentation; no separate use of
`lem-weil-pbc-finite-presentation-base-change-composition` is required.
The two existing tool approvals (fibre stalk quotient and closed-fibre criterion)
are still used and preserved.

## Where the brief, the DAG or earlier work was wrong

The current item DAG cites two unstated nodes as proof dependencies:
`lem-sfb-fibre-flatness-compatible-stalk-data` and
`lem-sfb-flat-closed-fibre-approximation-rigidity`. Both have no Lean attachment
and no module, contrary to the brief's readiness premise. This was resolved by
proving the required constituent arguments directly; no tool workaround or
new sorry was needed. The statement itself agrees with Stacks Tag 039C for the
structure sheaf. Tags 039C and 05UV were read in the local Stacks sources.
The current unit route was preserved; the changes are below the unit level.

The shorter-route searches were run with msearch.py (LeanFinder, Loogle, grep)
and rg over Mathlib, Sheaf, and WeilConjectures. They found existing stalk finite
type, faithful flatness and localization tools, but no direct theorem with this
scheme statement. Edge cases: a field base and identity approximation satisfy
the construction; nonzero stalk rings provide the rank-one nontriviality needed
by the local criterion, and no global flatness assumption was introduced.

Repair of the return at e329d985b: the former scheme-square helper duplicated
a private theorem in
`WeilConjectures.AlgebraicGeometry.PolynomialChartClosedFiberModuleFlat`. That
declaration is private, so importing its module cannot expose it. The retained
helper is genuinely generalized to arbitrary locally ringed spaces, with all
space and point binders explicit, and the criterion applies it to the underlying
locally ringed spaces via `toLRSHom`. Its proof uses Mathlib's locally ringed
space stalk API. The existing upstream private theorem, signatures, attributes
and public imports remain untouched. This changes only a newly introduced
private helper and its call site; no consumer or change record is required.
Compared the retained packet with current shared sources: the item still has
its original single hole, and no other module requires adaptation.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
