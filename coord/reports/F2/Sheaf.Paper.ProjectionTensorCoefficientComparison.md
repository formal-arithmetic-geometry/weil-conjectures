## What changed

Proved `WeilConjectures.CompactSupportCoefficientTensor.rational_existsUnique`, the
item's sole remaining hole, with its original signature and normalization. The existing
`comparison` definition is unchanged.

First prove naturality of the existing integralComparison. Restrict a normalized model's
chi to constructible pairs, invert it componentwise, and compose its coefficient image
with ordinaryComparison. The coefficient datum's integral_identity supplies the two
ambient functor equalities. The prescribed underlying homs of integralComparison agree
with this natural isomorphism, so faithfulness of the full inclusion proves naturality.

The new, fully proved module `Sheaf.Paper.ProjectionRationalTensorDescent` then descends
any such integral natural isomorphism. It verifies the coefficient and tensor restriction
equalities at scalar 1. Product-localization precomposition is fully faithful, giving
existence on all rational morphisms. The preimage equation gives precisely the requested
HEq normalization; unchanged integral objects give uniqueness. No extra additivity or
linearity assumption is imposed on the arbitrary normalized rational comparison R.

Only the item, the new helper module, their DAG nodes, and this report are delivered.
Existing public signatures, definitions, public imports and global attributes are unchanged.
The new helper uses local irreducibility controls to avoid expanding derived category and
scalar-action implementations while checking the localization argument.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.CompactSupportCoefficientTensor.rational_existsUnique`
(node `def-sf-projection-tensor-coefficient-comparison`). The other existing ordinary and
integral proofs are preserved.

Added 0 holes. The new public theorem
`WeilConjectures.CompactSupportCoefficientTensor.rationalTensorDescent`
(node `lem-sf-projection-rational-tensor-descent`) is proved completely. There are no
`sorry` declarations in either delivered Lean module. This is a proof, not a decomposition
into new unproved statements. Imported project theorems may still have their existing holes.

Validation: `lcompile.py --all` accepted both final modules together, exit 0, with no
warnings or errors and the standard 60-second per-file acceptance check. The earlier
profiled descent helper compiled in 33.7 seconds. Delivery preflight is run by deliver3.py.

## No longer needed

Removed the redundant proof imports `Sheaf.Paper.QcqsCompletionUnitCriterion`,
`all Sheaf.Paper.RingedTopoiCanonicalTensorPullback`, and
`all Sheaf.Paper.ProjectionCoefficientTensorTotal`. The last module remains a public
import, since its public definitions occur in the item's statements.

Removed five unused private helpers in `ProjectionTensorCoefficient`: `inverseSquare`,
`totalComparison_naturality`, `representativeSquare_iff`, `exists_pair_of_chain`, and
`completionUnit_comp_isIso`. A source search found no external users of these
private helpers. Their work, where needed, is already performed by the retained
ProjectionTensorNormalization and ProjectionTensorModelComparison proofs.

No whole module or DAG node is withdrawn. In particular the removed direct proof imports
remain used by the retained helper modules; their dependencies are not claimed as globally
pruned. All existing declared dependencies remain mathematically needed along that route.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or definition repair was needed. The old final DAG step merely said
the rational theorem remained a hole. It now records the integral naturality argument and
the complete rational localization proof. The current blueprint presents field-stage
transport concisely; the old step-13 terminology refers to the detailed comparison already
recorded in this item's node and docstrings.

The descent argument also covers zero objects and arbitrary normalized R: it uses no
cancellation of noninvertible integral numerator maps and no unrecorded integral lift of
a rational Weil structure. Localized inverse components come from the given integral
natural isomorphism. Coefficients and denominator maps are fixed by categorical localization.

## New nodes

`lem-sf-projection-rational-tensor-descent` records
`WeilConjectures.CompactSupportCoefficientTensor.rationalTensorDescent` in
`lean/Sheaf/Paper/ProjectionRationalTensorDescent.lean`. It states and proves descent of
an arbitrary integral coefficient tensor natural isomorphism, with its exact component
normalization and uniqueness. It depends on the existing coefficient and rational tensor
data, raw scalar localization, product localization and fully faithful precomposition.
No new statement is left unproved, and no change record is required because no existing
interface or data definition changes.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
