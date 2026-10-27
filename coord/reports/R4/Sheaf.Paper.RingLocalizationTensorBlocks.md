## What changed

Proved `CategoryTheory.ringLocalizationTensor_blocks` without changing its signature or any definition it uses. The proof constructs the two-row coordinates from the tensor-total coproduct, computes the differential on the two inclusions with the signed Mathlib total-complex API, and computes the augmentation on the surviving degree-zero row.

Added the fully proved utility module `Sheaf.Paper.RingPointTensorComparison`, which constructs the evaluated tensor comparison and proves its naturality and unit normalization. The comparison uses the sheafification adjunction and the existing source-library tensor presentation. An expensive general IsIso inference was replaced by an explicit inverse and its two identities. The utility module was then extracted to satisfy the 60-second per-file limit. All other helpers are private. No existing module besides the item was changed.

The main module privately imports the utility module and Mathlib's module biproduct comparisons. The utility module privately imports the adopted sheaf tensor naturality API. The original node and the new utility node describe this argument. The public item signature was checked byte-for-byte against the original. Both modules compile cleanly with `lcompile.py --all`: 31.2 seconds for the utility and 44.5 seconds for the item.

## Proved and sorry left

Closed: `CategoryTheory.ringLocalizationTensor_blocks` (node `lem-weil-pbc-ring-localization-tensor-blocks`), the item's one original hole. Added holes: none. Remaining holes in either delivered module: none. No split-off unproved statements. The new comparison, its inverse identities, naturality and unit formula are all proved.

## No longer needed

No original imports, nodes, or modules were removed. Both declared definition dependencies remain necessary. The new utility module packages a proved part of the original first step; it adds no pending mathematical work.

## Where the brief, the DAG or earlier work was wrong

No statement repair was necessary. The calculation follows the original three-step plan. Tag 0996 supplies the surrounding localization argument; the signed tensor calculation is the More on Algebra alternating-Cech convention already cited in the declaration. No cancellation or nonzero-ring assumption is used, so the construction also covers a zero section and the zero ring.

The older stage document forbids file splitting, but the explicit current brief permits it after improving slow definitions. This delivery follows that current instruction: it first replaces costly invertibility inference by explicit inverse data, then extracts the self-contained, fully proved comparison.

## New nodes

`lem-weil-pbc-ring-point-tensor-comparison`, in `dag/nodes/sec-proper-base-change/`, records the evaluated tensor isomorphism, its naturality and its unit formula in `Sheaf.Paper.RingPointTensorComparison`. It is the first step of the original argument and is fully proved, with no sorry. No existing definition or statement was changed, so no change record or forced consumer adaptation is required.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
