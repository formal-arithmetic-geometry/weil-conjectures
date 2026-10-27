## What changed

Restored the assigned module from its quarantine archive, preserving its public import,
statement, Lean attachment and all hypotheses. Its sole theorem now obtains a shared
single-arrow projection comparison and applies the already proved generic
`ProjectionCoefficientTransport.composition_transfer` from
`Sheaf.Paper.RationalProjectionComparisonEquations`. A proof-only `import all` exposes
that private generic calculation; the rational coherence theorem and the sorried
rational mate-compatibility theorem are not used in the proof term.

Added `Sheaf.Paper.CommonProjectionTensorCompatibility`, stating compatibility of each
individual rational projection arrow with inclusion using one tensor natural
isomorphism for each space. This theorem has no projection-coherence hypothesis and
asserts no composition, refinement, pentagon or proper law. It supplies exactly the
single-arrow premise of the generic transport calculation. The family of tensor
isomorphisms is used only within a theorem proof; no definition chooses arbitrary data
from this existence statement. Updated the item's proof route and dependencies.

Validation: lcompile.py --all accepted both delivered modules with exit code zero
and no diagnostics. The original theorem signature is byte-for-byte unchanged.
The added dependency routes do not reach the item, so the reduction is noncircular.

## Proved and sorry left

Closed the original hole in `WeilConjectures.commonProjectionComposition_onStage`
(node `lem-sf-common-projection-composition-on-stage`) by a complete Lean proof from
`hH.composition`, the proved generic composition-transfer calculation, and the new
single-arrow comparison. The item's module has zero remaining holes.

Added one hole: `WeilConjectures.commonProjectionTensorCompatibility`
(node `lem-sf-common-projection-tensor-compatibility`). Its proof is exactly `by sorry`;
the docstring specifies the canonical tensorator construction, its naturality, the
proper and open transpositions, and the endpoint pasting argument. This is a
decomposition: one original hole closed, one strictly smaller hole added, net zero.
It is not an unconditional proof of the projection composition law.

The new statement is strictly a part of the argument: it compares one projection
arrow, without even assuming a finite-stage composition equation. The composition
algebra, support-compositor preservation, pullback-compositor preservation, naturality,
and endpoint cancellation are supplied by a separate existing proved calculation.

## No longer needed

No original public import was removed and no module is withdrawn. The new proof uses
the existing operation-stage, constructible-projection and coefficient definitions
through the retained public import and the transport helper. It no longer performs
its own representative-level tensor or pullback normalization calculation. Thus its
direct proof dependencies `def-weil-derived-pullback-tensor-hom`,
`def-pur-completed-pullback-tensor-comparison`, and
`def-weil-algebraically-closed-coefficients` move to the new single-arrow node's proof;
they remain mathematically needed there and are not globally pruned. The operation
and projection-mate definition nodes also remain needed through the signatures and
transport calculation.

The proof adds only the private proof import of RationalProjectionComparisonEquations
and the private proof import of CommonProjectionTensorCompatibility. It does not
import CommonProjectionComparisonEquations or CompactSupportProjectionFieldStages:
those consume this item and would be circular. The unit has no realized statement
or steps, and its route is unchanged. No node or module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The missing source was quarantined, not withdrawn. Its archive was used for restoration;
no deletion or empty-module replacement is proposed. The previously stated plan was
mathematically appropriate, but its composition algebra already exists as a proved
generic private lemma in RationalProjectionComparisonEquations, so redoing that algebra
is unnecessary. The actual remaining normalization obligation is compatibility of
individual projection arrows with one shared tensorator. Per-square exchange
comparison records alone do not provide a tensorator independent of the square;
the new lemma explicitly records this necessary normalization step.

Edge cases of that new step were checked against its construction: identity maps,
identity coefficient extensions, repeated fields, zero inputs and empty schemes use
the same scalar unitors, adjunction identities and common-stage representatives.
No faithfulness of inclusion, additional Tor assumption, properness of f or
separatedness of the structure schemes is assumed. The existence witness is only
used propositionally. No shared statement, definition or public import was changed.

## New nodes

`lem-sf-common-projection-tensor-compatibility` is the single-arrow portion of the
source's Compatibility argument. It states existence of one family of tensor natural
isomorphisms carrying each specified rational compact-support projection component to
its included common-stage component, through the existing source and target endpoint
isomorphisms. Its proof plan uses the canonical common-stage tensor and pullback/tensor
representatives, the prescribed adjunction comparisons and proper/open factorization.
LeanSearch, Lean Finder, Loogle and Mathlib grep searches found no theorem for these
specified coefficient-stage projection arrows. Local source search found and reused
the complete generic composition-transfer proof. There are no change records because
only the item, a new module and their DAG nodes are changed.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
