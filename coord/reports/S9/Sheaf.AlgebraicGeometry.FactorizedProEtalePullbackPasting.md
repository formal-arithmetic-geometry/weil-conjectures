## What changed

Filled both proofs in `Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting`.
Every existing declaration signature and every existing definition body is unchanged.
No source-library module was changed.

The pasting equality follows from the published derived-composition coherence at
`(u,rY,sY)`, `(rX,u,sY)`, and `(rX,sX,u)`. A private expansion helper allows a
specified composite arrow and equality proof, so all square transports are handled
by equality elimination. Precomposition with the invertible outer compositor and
cancellation combine the three equations. The entire calculation is a private generic
natural-transformation lemma; the public theorem specializes it with the three published
coherence equations. This avoids repeated evaluation of the concrete localization model.

For representatives, the unit-normalized ordinary compositor already comes with an
identity identifying its exact derived localization with the canonical derived
compositor. Private helpers apply the existing localization identities for inverses,
composition, whiskering, associators, and equality transports. Intermediate composition
comparisons cancel in each path. The resulting natural-transformation equations hold
on all derived objects and are evaluated at `DerivedCategory.Q.obj K`.

Updated the item's proof steps, proof dependencies, proof origin, and obsolete tool-use
entries to describe this route. No new node, public declaration, axiom, or definition
repair is introduced. The complete module compiles cleanly through `lcompile.py` in
5.6 seconds with the normal heartbeat and timeout settings. All existing declaration
signatures were also checked textually against the shared source, and every line is at
most 100 characters.

## Proved and sorry left

Closed the two original holes:

- `AlgebraicGeometry.Scheme.proEtaleFactorizedPullback_pasting`.
- `AlgebraicGeometry.Scheme.proEtaleFactorizedPullback_pasting_representatives`.

Both belong to `lem-pur-factorized-pullback-square-pasting`.
Holes added: zero. Sorries left in the item: zero. No split-off statements.
All private helpers are proved. The larger localization calculation is proved first
for arbitrary exact functors, then specialized to the concrete pro-etale operations;
this avoids repeatedly checking large concrete module-category terms in the kernel.

## No longer needed

Removed these direct imports:

- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`.

Removed direct proof dependencies and their obsolete `tool_uses` entries:
`lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-weil-pbc-proetale-derived-pullback-composition`,
`prop-weil-pbc-proetale-constant-ring-map`, and
`lem-trf-constant-coefficient-composition`.
The first is unnecessary because exact-localization normalization holds on all
complexes. The others are already incorporated in the published canonical compositor,
coherence theorem, and ordinary-normalization interface; the proof does not reestablish
them separately. Statement dependencies remain unchanged, as do all unit realizations.
No module or existing declaration is withdrawn, and these dependencies may still be
needed by other library consumers.

Retained `ProEtaleContinuousCohomologyLimit` because its published locally-bijective
site instance is used when elaborating the existing flatness hypothesis.

## Where the brief, the DAG or earlier work was wrong

The representative proof plan asked for repeated K-flat-preservation applications.
The existing ordinary-normalization theorem is stronger: it identifies the canonical
compositor as an exact-localization natural isomorphism on the entire unbounded derived
category. Thus the representative formulas follow without using the supplied K-flatness
or flat-term assumptions. Their original hypotheses and conclusions are preserved.
The three-coherence route for the main pasting statement is retained.

Searches used Lean Finder, Loogle, the logged grep service, and local searches in Mathlib
and both library roots. The useful existing declarations are the published coherence and
ordinary-normalization theorems and the localization identities in
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`; the general
pseudofunctor candidates did not give a shorter route for these specified comparisons.

The public-import and module-command audit is recorded in
`coord/changes/s9-factorized-proetale-pasting-imports.md`. The downstream utility returned
no consumers, and direct library searches found no external references requiring
adaptation. The first preflight requested this record; it is supplied in this packet.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
