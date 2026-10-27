## What changed

Added the proof-only module `Sheaf.AlgebraicGeometry.DiscretePointPresentationTransport`,
which isolates the section reconstruction and finite-cokernel transport step as a named
intermediate theorem. The item module now applies that theorem and a local refinement
lemma. The refinement uses the existing finite local matrix lifting API and preserves the
specified ranks `m` and `n`; the empty-sieve case is handled by the zero object. The new
transport theorem remains a documented split-off `sorry`, while the item theorem is proved
from it and the existing declarations.

Both modules compile with `lcompile.py --all`; the final compile completed without errors.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_point_presentation_refinement`
(node `lem-sfb-discrete-point-presentation-refinement`). There are zero holes in the item.
Added one hole in
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_point_presentation_transport`
(node `lem-sfb-discrete-point-presentation-transport`). This is a decomposition, not a net
hole reduction. One hole was split
off as `discrete_point_presentation_transport` in node
`lem-sfb-discrete-point-presentation-transport`; it is the strictly smaller transport step.
No `sorry` occurs inside a definition.

## No longer needed

No original public import is removed. The direct proof does not need
`lem-sfb-finite-local-section-lifts` / `Sheaf.CategoryTheory.FiniteLocalSectionLifts`: its
role is supplied by the already proved upstream constant finite-module Hom lifting, through
`exists_sieve_overMap_maps` in `Sheaf.Paper.SiteFiniteConstantComplexDescent`.
It also does not need `lem-cbc-sieve-module-sheafification` as a separate proof import:
the existing constant-sheaf and cokernel comparison API supplies its role.

The direct dependencies `def-sfb-constant-sheaf-scheme-pullback-comparison`,
`def-sfb-integral-models-stacks-data`, `det-def-sfb-constructible-local-model`, and
`lem-weil-proetale-weakly-etale-localization` are retained below the new transport node,
rather than imported directly as proof dependencies of the item. They are not globally pruned.
No module is withdrawn or claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The two original DAG steps were both still unproved. This delivery proves the second step
using existing proved private helpers and isolates the first step. The transport portion is a separate, strictly simpler statement,
so it is recorded as a new node and module. The item node's proof dependencies and steps were
updated to reflect this route.

## New nodes

`lem-sfb-discrete-point-presentation-transport` records the transport of the given point
cokernel to a cokernel of a constant k-module map on the slice. Its Lean declaration is in
`Sheaf.AlgebraicGeometry.DiscretePointPresentationTransport`.

The proof-only `import all Sheaf.Paper.SiteFiniteConstantComplexDescent` accesses its
proved helpers `exists_sieve_overMap_maps`, `constantOverMapIso`, and `over_sheaf_isZero`.
These helpers are complete proofs; no new assumption or complex-descent hypothesis is used.
The helper module is used as a generic site tool, without bypassing an integral-model unit.
The theorem itself is not called. No shared module, definition, or public interface changed.

Edge checks for the transport statement: zero rings and empty schemes still have their
regular and zero free modules; m=0 or n=0 use the same finite coproduct and cokernel
constructions. Arbitrary c is deliberately allowed: its inverse identifies the regular
coefficient module with the constant k-module, but it need not make d globally scalar.
The latter issue is resolved by the fully proved local refinement, not assumed in transport.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
