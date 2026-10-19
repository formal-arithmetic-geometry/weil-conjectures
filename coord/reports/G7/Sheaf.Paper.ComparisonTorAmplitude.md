## What changed

Completed `AlgebraicGeometry.finiteCoefficient_comparison_reflects_torAmplitude`
from the existing `AlgebraicGeometry.ProEtale.comparison_torAmplitudeIn_iff`.
The coefficient ring is finite by the positive-level finiteness theorem. The given
bounded-below hypothesis packages the original object into the plus category.
`Functor.mapDerivedCategoryCompIso` identifies the intrinsic derived comparison
with intrinsic realization after termwise site comparison. The supplied isomorphism
then transports each universal K-flat tensor test to the original Tor hypothesis.
All theorem signatures remain unchanged. Clause (i) is unchanged.
Updated the item's proof steps and dependencies to describe this shorter route.

Repaired both points of reviewer C-f9008's return: removed the unused retired
`Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` public re-export (H9),
retaining its `WeilConjectures` counterpart, and replaced clause (ii)'s proof
docstring with the requested description of the implemented argument (H8).
Corrected the earlier claims that all public imports were preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.finiteCoefficient_comparison_reflects_torAmplitude`
(node `lem-sf-comparison-tor-amplitude`).
The existing proof of
`AlgebraicGeometry.finiteCoefficient_comparison_preserves_torAmplitude` is retained.
Zero holes added, zero split off, zero `sorry` left in the item module.
The existing imported `comparison_torAmplitudeIn_iff` remains an independent
unproved dependency; it is not a new hole or statement in this delivery.
The repaired module compiled without errors or warnings (3.8 seconds).
The repair dry run passed compilation and preflight (commit `b0875a21df`),
classified as CODEX for the changed node, removed direct unit-route import,
and returned-delivery repair. That unit-route module remains imported through
the generic comparison theorem, as detailed below.

## No longer needed

Removed the unused public import
`Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, a retired re-export;
the existing public import of
`WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` stays.

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`: its sheaf-unit
  argument is already packaged in the general comparison Tor-interval theorem.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`: its predicate is already public
  through the statement dependencies.

The direct proof dependencies `def-kun-tor-amplitude`,
`def-weil-pbc-site-comparison-morphism`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, and
`prop-weil-pbc-site-comparison-finite-level` are no longer separately needed
here; reflection is supplied by `lem-exc-comparison-tor-interval`. These nodes can
still be needed by that general theorem and are not globally redundant.
Removed obsolete top-level tool approvals for the generic tensor-pullback theorem,
the finite-level site theorem, lifted algebraic adjunctions and sheaf algebraic
structures. Clause (i)'s existing dependencies remain needed through its two
component theorems. The statement-level imports remain available through the existing
WeilConjectures interface; the retired Sheaf re-export is removed because it is unused.
The removed finite-level comparison import stays in the import closure through
`Sheaf.AlgebraicGeometry.ComparisonTorInterval`; its node remains in that theorem's
proof dependencies. Thus the sheaf-unit step of proper base change is retained.
No whole module is withdrawn.

Removed the unused DAG dependency `lem-weil-pbc-exact-functor-derived-functor` and
its obsolete tool approval. The proof uses the already proved source declaration
`CategoryTheory.Functor.mapDerivedCategoryCompIso`, rather than the Kan-extension
theorem recorded on that node. Its application and the isomorphism transport are
ordinary coherence glue, recorded explicitly in the proof step.

## Where the brief, the DAG or earlier work was wrong

The planned clause (ii) proof repeats the converse of the already stated generic
finite-ring comparison Tor-interval equivalence. Reusing that declaration requires
only derived-composition coherence and transport under the given isomorphism.
The bounded-below hypothesis is exactly the one required by that declaration;
its ordered-interval hypothesis follows from the existing pro-etale Tor predicate.
The library statements, coefficient ring, universes and target meanings are unchanged.
The import-direction tool permits this dependency and a dependency traversal
confirmed no DAG cycle. LeanFinder and Loogle found no direct Mathlib theorem;
local source search found the generic library equivalence used here.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
