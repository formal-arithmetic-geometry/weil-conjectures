## What changed

Prove `AlgebraicGeometry.Scheme.qbar_properBaseChange` from actual integral preservation,
finite-stage invertibility, and the existing scalar-compatible descent interface.
The four operation witnesses are constructed from their published operations.
The existing statement is unchanged. The exchange and finite-stage representative
definitions are factored through generic constructions with exactly the original
formulas, preserving their values by definitional equality. A normalization comparison between
actual completed exchange and the strict-tower exchange is isolated as a separate result.

## Proved and sorry left

The original module had one hole: `AlgebraicGeometry.Scheme.qbar_properBaseChange`.
The retained proof has no `sorry`. The new theorem
`AlgebraicGeometry.Scheme.pbcActualCompletedExchange_transport` has one `sorry`, node
`lem-weil-pbc-actual-completed-exchange-transport`. This is a decomposition: one upper
hole closed and one strictly separate normalization-comparison hole added, net zero.
It assumes no properness, constructibility or dimension bound, proves no descent, and
is not a renamed version of the item. All private helpers are proved, including the generic
localization-and-isomorphism transport lemma and the generic stage-system assembly
and overfield formulas. The existing isomorphism-of-descent theorem handles invertibility;
a generic proved lemma handles identity cancellation in the overfield formula. These avoid rewriting endpoint equalities through the concrete categorical term.

## No longer needed

Remove private imports `Sheaf.Paper.FiniteExtensionProperBaseChange`,
`Sheaf.Paper.CommonStageCalculus`, and `Sheaf.Paper.IntrinsicQbarCategory`.
The corresponding direct proof dependencies `thm-weil-pbc-finite-extension` and
`prop-weil-pbc-common-stage-calculus` are unnecessary for this argument: generic
actual-coefficient preservation and complete-pro-etale exchange apply directly to
the canonical small coefficient datum, and the source library already proves the
required stage-inclusion and descent formulas. No upstream declaration is withdrawn.
The finite-stage pair category, scalar compatibility and descent remain needed.
These modules still have other importers, so no global module-pruning claim or deletion
is made. No module deletion is requested.

## Where the brief, the DAG or earlier work was wrong

The finite-extension theorem uses the unlifted padic coefficient datum, whereas this
item uses the canonical small field with lifted integral ring and the actual completion
reflector. It cannot be applied directly without a normalization comparison. The new
lemma states this comparison at arbitrary adic coefficients; the strict completed
exchange is already covered by `completeProetale_isIso`.

The latest blueprint text under `thm-weil-pbc-qbar` now concerns Weil structures.
The assigned existing Lean signature and the target signatures are preserved verbatim;
this packet proves the assigned finite-stage pair-category statement.

## New nodes

`lem-weil-pbc-actual-completed-exchange-transport` compares the two already published
completed-exchange constructions by their ordinary adjunction and completion units.
The docstring gives the argument and checks that no properness, boundedness,
constructibility, nonempty-scheme or nonzero-object assumption is needed. Its public
statement is in `Sheaf.Paper.PbcActualCompletedExchangeTransport`.

The definition factoring and scoped proof commands are documented in
`coord/changes/G1-qbar-proof-context.md`; existing public signatures and mathematical values are preserved.

Validation: the item compiled without warnings in 33.7 seconds; both packet modules
also compiled together. The sole unchanged downstream consumer,
`Sheaf.Paper.GeometricFiberQbar`, compiled in 5.0 seconds against the packet.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
