## What changed

Proved `WeilConjectures.podReindexing_hom_resolution_model` by decomposing its
underived and derived comparison argument into two strictly smaller named theorems in
the same module. `podReindexing_tensor_hom_data` packages the normalized tensor and
ordinary sheaf-Hom comparisons and their section formulas. `podReindexing_derived_hom_data`
packages the actual Hom-complex, projection, naturality, quasi-isomorphism, and
localization-resolution model laws. The target theorem combines these packages in the
required existential order. Existing declarations, imports, and the target statement
remain unchanged.

The delivered module compiles with `lcompile.py` in 35.2 seconds. The two split-off
statements remain explicit `sorry` theorems; no `sorry` occurs in a definition.

## Proved and sorry left

Closed the original hole in `WeilConjectures.podReindexing_hom_resolution_model`.
The proof is the complete existential assembly from the two strictly smaller comparison
statements.

Added two split-off holes:

- `WeilConjectures.podReindexing_tensor_hom_data`, node
  `lem-pod-reindexing-tensor-hom-data`.
- `WeilConjectures.podReindexing_derived_hom_data`, node
  `lem-pod-reindexing-derived-hom-data`.

Holes closed: 1. Holes added: 2. Sorry left: 2.

## No longer needed

None. The existing imports and declarations in the assigned module remain needed. No
existing module or public declaration was withdrawn; the split statements are in the
assigned module so the recorded Lean attachments of the original item stay unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing proof route was too large to fill directly in the assigned theorem within
the available interface. The two intermediate statements are genuine subarguments:
the first contains only tensor and underived Hom data, while the second contains only
the derived Hom-complex and localization laws. Their statements are strictly smaller
than the parent and the parent proof is a real constructor application, rather than an
alias of the parent statement.

## New nodes

- `lem-pod-reindexing-tensor-hom-data`: `podReindexing_tensor_hom_data`.
- `lem-pod-reindexing-derived-hom-data`: `podReindexing_derived_hom_data`.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
