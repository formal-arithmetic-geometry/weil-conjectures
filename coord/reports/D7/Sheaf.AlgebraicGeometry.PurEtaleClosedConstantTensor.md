## What changed

Proved `AlgebraicGeometry.Etale.closedConstantModule_flat` in
`Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor`, with its statement and all definitions
unchanged. The proof applies the existing geometric-stalk flatness criterion. On the closed
support, the stalk is the free rank-one coefficient module; outside the support, restriction
to the open complement vanishes. The canonical universe-lift comparisons connect the stalk
APIs without changing any construction.

Added private proof imports of `WeilConjectures.SixFunctors.OpenClosed.Vanishing`,
`WeilConjectures.SixFunctors.OpenClosed.Points`, and
`WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat`. Updated step 6 and its dependencies in
`lem-pur-etale-closed-constant-tensor` to record this argument. No public signature,
definition, attribute, or target changed.

Validation: the complete item module compiled through `lcompile.py` in 15.6 seconds.
The proof assumes neither a nonzero coefficient ring nor nonempty supports.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.Etale.closedConstantModule_flat`
(node `lem-pur-etale-closed-constant-tensor`).

One original hole remains unchanged:
`AlgebraicGeometry.Etale.closedConstantTensor`
(node `lem-pur-etale-closed-constant-tensor`). Its ordinary pullback/tensor and derived
coherence clauses have not been proved by this delivery. This is a partial delivery of one
of the module's two theorems, not a decomposition of the bundled theorem.

Added zero holes and split off zero statements.

## No longer needed

None. The original proof-dependency imports and the other eight proof steps are retained
for the unfinished bundled theorem. No module or mathematical dependency of that theorem
is claimed to be unnecessary.

## Where the brief, the DAG or earlier work was wrong

The source library already proves the required stalkwise flatness criterion, so step 6 need
not rebuild exactness and conservativity on short exact sequences directly. No mathematical
statement error was found. Ordinary geometric points live in a smaller universe than the
coefficient modules; the canonical `uliftSheafFiberIso` is necessary when combining the
closed-direct-image and constant-stalk comparisons. The proof unfolds `closedConstantModule`
explicitly once, respecting its existing local irreducibility declaration.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
