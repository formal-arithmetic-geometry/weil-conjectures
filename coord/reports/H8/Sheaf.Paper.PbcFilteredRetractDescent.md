## What changed

Proved `AlgebraicGeometry.Scheme.pbcFilteredRetractDescent` with its original
signature in `Sheaf.Paper.PbcFilteredRetractDescent`. The proof obtains an
idempotent on the specific object `X.toStage h` at one finite stage, splits it
using the given `hC`, and includes its splitting into the pair category through
`isoToStage`. The same splitting proves idempotent completeness and every
additional finite-stage and composite equation in the statement.

The existing `WeilConjectures.CategoryTheory.StageSystem.IdempotentComplete`
proves the general completeness assertion. Its `exists_conj_ι_idem` chooses
an iterated transition object and an arbitrary comparison isomorphism; the
stronger present conclusion specifies `X.toStage h` and `isoToStage X h`.
The short direct use of its underlying generic representative and transport
API supplies precisely this extra information without another import.

Updated the theorem's proof docstring and node's proof, proof dependencies and
proof origin to match the Lean argument. No signatures, definitions or public
imports changed. No consumer adaptations or change records are needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.pbcFilteredRetractDescent`
(node `prop-weil-filtered-retract-descent`).

Zero holes remain in the item. Zero holes added; zero statements split off.
The single-file server compile passed without warnings (25.7 seconds).
The proof uses the original finite-stage idempotent-completeness hypothesis;
it does not assume representatives are already idempotent before refinement.

## No longer needed

Removed proof imports `Sheaf.Paper.CommonStageCalculus` and
`Sheaf.Paper.PbcScalarExtension`, and removed their proof dependencies
`prop-weil-pbc-common-stage-calculus` and `prop-weil-pbc-scalar-extension` from
this node, including its obsolete tool-use entries. The fully proved generic
StageSystem API already available through `FiniteStagePairCategory` supplies
composition, eventual equality, transport functoriality and inclusion formulas.
The shift/additive calculus and the separate scalar-extension coherence package
are unnecessary for this proof. This is pruning of this item's dependencies;
other parents can still need these modules.

The optional `thm-weil-pbc-finite-stage-karoubian` /
`Sheaf.Paper.PbcFiniteStageKaroubian` remains unnecessary: completeness of the
finite stages is explicitly assumed. No new proof import was added.

## Where the brief, the DAG or earlier work was wrong

The planned passage through normalized scalar units is unnecessary. The generic
pair-category construction supplies `isoToStage` and `mkHom_eq_isoToStage` for
arbitrary coherent transition functors, and these give all requested equations.
No mathematical statement was disputed or changed. The unit record has empty
realized statement and step lists; the representative/refinement/splitting route
of the original proof is retained.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
