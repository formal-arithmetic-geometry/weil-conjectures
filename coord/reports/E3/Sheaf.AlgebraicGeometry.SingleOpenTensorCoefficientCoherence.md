## What changed

Restored `Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence` from the
quarantine path assigned by `coord/rework.tsv`. Removed `derivedPullback` from
one local `irreducible` attribute command: the current upstream declaration is
already an `irreducible_def`, and Lean rejects applying that attribute again.
This repairs an actual compiler error. A proof-only import of the existing
`PerfectHomCochainCounit` API names the same selected counit via
`perfectHomTensorCounit` in the private normalization and naturality helpers.

The public theorem signature and proof, all docstrings, and every existing
import are identical to the archived source. The private helper changes replace
two literal nested-choice expressions with their existing definitionally equal
counit name; no construction or mathematical assumption changes. The existing normalization, naturality, tensor-composition
associativity, and final monomorphism-cancellation proof is preserved. The
existing node and its two proof dependencies are unchanged. Change record:
`coord/changes/E3-single-open-tensor-restore.md`.

The final item compiled cleanly in 37.3 seconds under the normal 60-second
limit. The exact delivery axiom probe completed in 40.7 seconds, reporting
`SHEAF-PROBED 2` and no forbidden axiom or hidden hole. Its generated overwidth
probe line is outside the delivered source. The public theorem signature and
proof are unchanged, and no declaration is added or removed. All delivered
source lines satisfy the 100-character limit.

Compiled the repaired item together with its unchanged archived direct consumer,
`Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow`: 39.0 seconds and
28.7 seconds respectively, both clean. The consumer was checked against the new
sandbox artifact, not the published item's older artifact. Its unchanged
`StandardSingleBaseChangeMap` prerequisite and the current source version of
`DerivedBaseChangeSourceIso` were also compiled for that check. These test-only
copies are not delivered; no other module is adapted.

## Proved and sorry left

`AlgebraicGeometry.single_open_tensor_coefficient_coherence` retains its complete
proof, attached to `lem-pc-single-open-tensor-coefficient-coherence`.

This is a compatibility repair of a proved archive: original holes 0; holes
closed 0; holes added 0; holes remaining 0; statements split off 0. Every private
helper is proved. No `sorry` is introduced in any module.

## No longer needed

No existing imports, nodes, or modules are pruned. The added proof-only import
only supplies an abbreviation for the already selected counit. Both declared proof dependencies remain
used: `lem-sc-picard-termwise-single-map-composition` and
`lem-pc-tensor-pullback-composition-associativity`. The existing unit route and
the quarantined parent `StandardSingleOpenRelativeArrow` are preserved.

LeanFinder, Loogle, the supplied Mathlib grep search, and local source searches
found generic functoriality, single-complex, and tensor-composition tools rather
than a shorter theorem giving this normalized coordinate identity. The existing
proved categorical argument is retained without new obligations.

## Where the brief, the DAG or earlier work was wrong

The module was absent because of quarantine, not because its mathematics was
withdrawn. Its archive already contained a complete proof. The current upstream
reducibility declaration makes the old local attribute invalid. Removing that
single redundant attribute fixes the compiler error. Naming the same counit
through the existing source API also avoids spelling out its nested witness
selection in the private helper statement and proof. The final source and
axiom probe both fit the unchanged per-file limit; the mathematical proof
dependencies are preserved. Zero modules are withdrawn and no hollow definition is added.

The proof uses only the explicitly assumed invertibility of the final comparison
for `r`; it does not require flatness or invertibility for `q` or `t`. The
categorical proof covers zero modules, empty schemes, and identity maps.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
