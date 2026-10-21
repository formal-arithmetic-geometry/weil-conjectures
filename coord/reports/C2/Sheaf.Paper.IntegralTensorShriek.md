## What changed

Repaired the no-op returned packet against the current live source. The module is already
restored and fully proved, so a second restoration would change nothing. This delivery
instead removes the unused private import Sheaf.Paper.ProfinitePointPullback and its
proof-dependency edge, replaces a repeated extension-product induction with Mathlib's
ObjectProperty.extensionProductIter_le_of_isTriangulatedClosed₂, and shares the open
preservation proof between the open and locally closed cases.

Public signatures, definitions, public imports and local attributes are identical.
The node copy starts from the current library and updates only proof, proof_deps and
proof_origin. The integral-heart resolution and finite open/closed localization route
is preserved. Change record: coord/changes/C2-integral-tensor-shriek-proof-pruning.md.

The revised item compiles in 17.7 seconds without errors or warnings. A public-API
importer compiles in 3.0 seconds and prints only propext, Classical.choice and Quot.sound
for all three public declarations. Unchanged copies of all three direct consumers compile:
IntegralTensorPullback (17.2 seconds), IntegralTensorProduct (10.1 seconds), and
IntegralTensorInverseImage (31.4 seconds). The downstream tool confirms exactly these
three direct importers. The node's proof_deps equals the union of its proof-step uses.
No new test theorem or scratch importer is part of the delivery.

## Proved and sorry left

Zero sorry occurrences before and after this repair: 0 of 0 holes closed, 0 holes added,
0 split off. No declaration has a remaining sorry. The complete proofs of
AlgebraicGeometry.ProEtale.integralTensorShriek_preserves and
AlgebraicGeometry.ProEtale.integralTensorShriek_generated are retained and simplified.
AlgebraicGeometry.ProEtale.integralTensorShriek_pointComplex remains the same actual
termwise pullback construction. This packet claims dependency pruning and proof
maintenance, not new hole closure.

## No longer needed

Removed the private import Sheaf.Paper.ProfinitePointPullback and the direct proof
requirement lem-weil-pbc-profinite-point-pullback (including the local-model proof step's
uses entry). The proof uses the point inverse image and adjunction already present in
the public API; it never uses that module's additional coherence declarations.

The manual extensionProductIter induction is replaced by the existing Mathlib closure
lemma. No other import or node is removed. No entire module is withdrawn: other callers
may still need ProfinitePointPullback. All archived and live parent edges to this item
and its Lean attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

The old packet's statement that lean/Sheaf/Paper/IntegralTensorShriek.lean was absent is
stale. The current library already contains the complete archived source, exactly as
the return reports. The old restoration change record and restoration-only proof-origin
note have been replaced with records of the actual proof and dependency changes above.
The DAG also listed a direct profinite-point coherence dependency the Lean proof never
used. No mathematical statement defect or new node was found. No second reader was
started; the maintainer independently reviews this packet.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
