## What changed

Prove the specified quotient-successor square by comparing the ordinary tensor transition
with scalar insertion, restriction composition, and scalar balancing. Identify the normalized
derived balancing with the comparison obtained from uniqueness of left adjoints. The triangle
identity computes the transpose of the reduced counit; naturality transports the calculation
along the given representative isomorphism. The adjunction-composition calculation is a proved
public theorem in the new module
`Sheaf.Paper.AdicNormalizedScalarComposition`; the remaining helpers are proved private lemmas.
The public statements and the construction of the level isomorphism are unchanged.

Update the item's proof plan and dependencies to record this argument. No other existing
module or node is changed.

Validation: `lcompile.py --all` compiled both delivered files successfully, each within
the 60-second limit. The final source contains no profiling options or warnings.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.adicResidueQuotientTensorLevelIso_successor`.
One original hole closed, zero holes added, zero holes remaining in the delivered module.
No split-off holes. The new module and its private scalar-transition calculations are fully proved.

## No longer needed

No modules are withdrawn and no original imports are removed. The K-flat preservation and
exact restriction composition imports are now confined to the new helper module, where
the generic scalar calculations use them. The direct proof dependency
`lem-pur-change-of-rings-tensor-cancellation-independent` is replaced by the proved section
normalization API in `RingedScalarTensorSections`; its module remains a transitive dependency
of the original scalar tensor comparison. Thus this delivery claims no module pruning.
The unit's quotient-reduction route is preserved.

## Where the brief, the DAG or earlier work was wrong

No disputed statements or definition repairs. The informal plan suppressed the compatibility
between the chosen normalized adjunctions and the chosen scalar-composition comparison.
The proof supplies that compatibility using the K-flat computation formulas, ordinary
insertion of one, and exact restriction composition. No further unproved obligation is used
in place of the successor square.

## New nodes

`lem-sfb-adic-normalized-scalar-composition`: the specified derived balancing equals the
uniqueness comparison of the composed normalized adjunctions. Its theorem is proved,
with no `sorry`. It isolates the self-contained adjunction calculation so each file
can compile within the 60-second limit after the tensor-functor unfolding was improved.

The blueprint search for scalar composition and adjunction composition found no imported
blueprint statement of this normalization. The new node inherits the item's explicit
`det-lem-integral-models-stacks` ancestry and records the full intermediate chain.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
