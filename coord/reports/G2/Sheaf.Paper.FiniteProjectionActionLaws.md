## What changed

Replaced the eight proof bodies in `lean/Sheaf/Paper/FiniteProjectionActionLaws.lean` with
categorical arguments using the adopted source library. The eight public theorem signatures,
the coefficient-finiteness instance, the public associator definition and all public imports
are unchanged. No file under `lean/WeilConjectures/` is changed.

The private helpers derive pullback tensor associativity from the source's general
left-derived comparison, invert it, and transport it through the exact-pullback comparison.
Proper projection action follows by cancelling the mapped associator in the adjunction
projection-associativity identity. Open action follows by inverting the open projection
isomorphisms. The open-counit identity follows by the adjunction Hom equivalence and its
triangle identities.

For compactifications, a proved generic calculation combines the component families of the
proper projection, inverse open projection and pullback-composition comparison. Proper
naturality moves the open factors across the second proper projection; the two action
identities and tensor-composition coherence then give the result. The actual canonical maps
are identified using their component formulas. The private interface retains the three canonical tensor bifunctors and their associators,
with proved defining-equality certificates. A component-identification lemma rewrites the
three occurrences of the actual projection map while retaining the composite functor objects.
This avoids unfolding concrete derived-category constructions during kernel conversion.
No entire derived natural-transformation structure is passed to the action calculation. The coefficient-category identities are specialized
to the prescribed finite coefficient ring.

Added private proof imports:

- `Mathlib.Tactic.CategoryTheory.Monoidal.Basic`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal`
- `WeilConjectures.CategoryTheory.Monoidal.Conjugate`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal`

Updated the existing node's proof, proof dependencies, proof origin and obsolete tool uses to
follow this route. There are no new public declarations, nodes, statement repairs, definition
repairs, withdrawn modules or forced adaptations. The proof elaboration scopes and the
unchanged consumer interfaces are documented in
`coord/changes/g2-finite-projection-action-laws-proof-scopes.md`, as required by preflight's
module-command check. The three downstream modules need no adaptation.

## Proved and sorry left

Replaced all eight original `sorry` bodies, with no holes added or split off:

- `AlgebraicGeometry.ProEtale.finiteProjectionAction_proper`
- `AlgebraicGeometry.ProEtale.finiteProjectionAction_open`
- `AlgebraicGeometry.ProEtale.finiteProjectionAction_compactification`
- `AlgebraicGeometry.ProEtale.finiteProjectionAction_open_counit`
- `AlgebraicGeometry.Etale.finiteProjectionAction_proper`
- `AlgebraicGeometry.Etale.finiteProjectionAction_open`
- `AlgebraicGeometry.Etale.finiteProjectionAction_compactification`
- `AlgebraicGeometry.Etale.finiteProjectionAction_open_counit`

Sorry left: none. Holes added: none. Split-off statements: none.
Validation: the complete eight-law module compiled on the authorized server in 42.5 seconds.
The axiom probe for every one of the eight declarations reports exactly `propext`,
`Classical.choice` and `Quot.sound`. The generic component calculation also compiled separately;
the ordinary etale compactification specialization compiled in 16.7 seconds. The cleaned module at its final library path also compiled without warnings in 46.7 seconds.
Cleanup removed one redundant private import, scoped unused section variables out of
certificates and wrapped the one overlong line. Delivery runs the complete module compiler
and preflight again.

## No longer needed

Removed these direct private imports:

- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.DerivedPullbackTensorIso`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`

The new proof does not use these eight former lemma dependencies:

- `lem-coef-etale-open-tensor`
- `lem-kun-inverse-image-monoidal`
- `lem-pur-composite-relative-tensor-action`
- `lem-pur-derived-pullback-tensor-iso`
- `lem-pur-unit-adjunct-tensor-action`
- `lem-sf-open-tensor-normalization`
- `lem-sfb-ringed-derived-monoidal-comparisons`
- `lem-sfb-ringed-projection-tensor-composition`

The last removed import was redundant with the existing public import of the ordinary
etale upper-star monoidal API. No module is withdrawn or deleted.

The general source adjunction and derived-functor APIs supply the needed coherence directly.
The three definition dependencies for the specified maps and compact-support construction
are retained. Statement dependencies and the blueprint unit route are unchanged.

Removed the item's old top-level tool uses, which the new proof does not invoke:

- `lem-sf-open-tensor-normalization`
- `lem-sf-ringed-derived-closed-symmetric-monoidal`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-pbc-extension-by-zero-adjunction`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-kun-derived-pullback-composition-monoidal`
- `lem-sfb-ringed-derived-monoidal-comparisons`
- `lem-sfb-ringed-projection-tensor-composition`
- `lem-coef-etale-open-tensor`

These removals concern this item's proof edges and direct imports. No adopted declaration or
module is deleted; other consumers and transitive imports retain their dependencies.

## Where the brief, the DAG or earlier work was wrong

The old planned route was longer than the current source-library route: the adopted library
already has the generic projection-associativity and derived tensor-composition results
needed here. The statements themselves were not found false or unusable. The normalization
of the compactification equality is needed for kernel performance; it does not replace or
change the specified isomorphism. No projection invertibility, boundedness or constructibility
hypothesis is introduced.

The launcher's default local mirror lacks the root `Mathlib.olean` needed by this import
closure. Server checks and delivery therefore use `LCOMPILE_NO_LOCAL=1` through the authorized
launcher tools. Busy-server responses were retried; they are not compilation results.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
