## What changed

Filled both proofs in `lean/Sheaf/Paper/SfCommonStageWeilCohomology.lean`, keeping
all existing signatures, definitions, visibility and imports unchanged.

`sfTruncationShift_existsUnique` compares the canonical truncation triangle of
K[1] with the shifted truncation triangle of K, at cuts (0,1)/(1,2) and
(-1,0)/(0,1). Mathlib's `TStructure.triangle_iso_exists` supplies the triangle
isomorphisms. Its triangle shift negates the maps, so the chosen middle
isomorphism is minus the identity; the first and third components then satisfy
the exact normalization equations in the statement. Upper uniqueness follows
from `to_truncLE_obj_ext` after composing with the inverse comparison; lower
uniqueness follows from `from_truncGE_obj_ext`.

`sfModelWeilCohomology_mem` unfolds the carrier of the existing pair functor,
uses the recorded common-stage heart identification, and applies the standard
truncation-bound instances and `isLE_shift`/`isGE_shift` to place degree n at zero.

The retained final file was checked against the current source and compiled cleanly
through `lcompile.py` in 4.8 seconds, with no errors or warnings. The resumed session
retained both completed proofs without changing any statement or definition, and
qualified the triangle names instead of adding a file-level namespace opening.

No new declarations or nodes were needed. Searches in the existing library and
Mathlib, and LeanFinder/Loogle searches through msearch.py, found the direct
Mathlib triangle comparison and truncation extensionality APIs. The item's node
has no numbered proof plan or proof dependencies; no planned route was replaced.

## Proved and sorry left

Closed 2 of 2 holes, with 0 holes added:

- `WeilConjectures.sfTruncationShift_existsUnique`.
- `WeilConjectures.sfModelWeilCohomology_mem`.

Both are attached to `def-weil-derived-cohomology-sheaves`. No `sorry` remains
in the item, and no other module is changed. The existing common-stage
standard t-structure and heart identification are used through their recorded
interfaces; their proof obligations remain in their existing modules.

## No longer needed

None. No imports were added or removed. The two existing public imports provide
the stated coefficient interfaces and retain the module's documented reexports.
The node has no declared proof dependencies to prune. The unit `sk-rem-rest` has
no realized statement or proof-step nodes, so the proof bypasses no unit step.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed repair. The generic instruction about numbered
DAG proof steps does not apply literally to this definition node: its `proof` and
`proof_deps` are empty. The supplied declaration docstrings give the argument,
which is implemented directly with Mathlib. The sign in Mathlib's triangle-shift
convention requires minus the identity on the middle term to obtain the unchanged
unit/counit normalization equations.

The first resumed dry run rejected the extra namespace opening as a command
change. It was removed; all triangle names in the proof are explicitly qualified.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
