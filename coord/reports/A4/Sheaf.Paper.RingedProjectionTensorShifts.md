## What changed

Proved `AlgebraicGeometry.Scheme.ProjectionRestriction.tensorComparison_shifts` in
`Sheaf.Paper.RingedProjectionTensorShifts`, with its statement unchanged. Added only
proved private helpers and private proof imports. No other Lean module, public
interface, target, definition, or statement was changed.

The proof derives ordinary naturality from `OrdinaryTensor.pure_unit`, constructs
the total-bifunctor comparison using the existing source-library API, and identifies
its inverse with the prescribed `totalMap`. The source library already proves both
signed shift compatibilities of this comparison. The normalization fields of the
tensor models make the representative identifications commute with shifts. The
representative equation of the supplied comparison then gives the desired square
on resolving complexes. Essential surjectivity of flat-term K-flat representatives
extends it in the varying argument, and naturality transports the fixed argument
to any derived object. All these steps are proved in Lean; no new obligations are
introduced.

Added `coord/changes/A4-ringed-projection-tensor-shifts-proof-context.md` for the
file-local elaboration context flagged by preflight. It records the unchanged
public signature, local attributes, proof imports, and all 1900 consumers; none
needs adaptation.

Updated the existing node's proof, proof dependencies, and proof origin to record
this route. The blueprint unit's statement and realized proof steps are retained.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Scheme.ProjectionRestriction.tensorComparison_shifts`
(node `lem-weil-pbc-ringed-projection-tensor-shifts`).

Holes added: 0. Holes remaining in the item: 0. Split-off statements: 0.
Every private helper is completely proved. This is a proof, not a decomposition.
The complete proof compiled through `lcompile.py`; the delivery command performs
the final compile and axiom/preflight checks after import and warning cleanup.

## No longer needed

The planned proof dependency `lem-sf-cochain-tensor-model-rigidity`
(`Sheaf.Algebra.Homology.CochainTensorModelRigidity`) is not used by this item:
essential surjectivity of the resolving localization and the existing
`NatTrans.CommShift.of_whiskerLeft` suffice. Its dependency edge is removed from
this node; no claim is made that the module is unused elsewhere, and no module
is withdrawn.

No original import was removed. Removed two exploratory proof imports already
publicly available through `RingedProjectionRestrictionData`:
`WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift` and
`Mathlib.CategoryTheory.ObjectProperty.Shift`.
No other planned dependency is pruned. The proof imports the existing total-bifunctor shift and shift-descent APIs, the
pure-tensor extensionality helpers, and the site/monoidal tensor comparison.

## Where the brief, the DAG or earlier work was wrong

The original plan was sufficient but asked for more than necessary: tensor-model
rigidity and fresh signed summand calculations can be replaced by essential
surjectivity and the already proved general total-bifunctor comparison shift
instances. No false statement or defective definition was found. The proof also
works for zero shifts, zero coefficient rings, and empty sites; it adds no
boundedness, nonzero, or nonempty hypothesis.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
