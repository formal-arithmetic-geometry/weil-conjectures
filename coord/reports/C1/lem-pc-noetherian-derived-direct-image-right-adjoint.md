Files written:
- `dag/nodes/sec-picard-framework/lem-pc-noetherian-derived-direct-image-right-adjoint.json` (item, split)
- `lem-pc-derived-qcoh-direct-sums` (statement-only, no Mathlib match)
- `lem-pc-derived-qcoh-compact-generation` (statement-only, no Mathlib match)
- `lem-pc-derived-direct-image-preserves-direct-sums` (statement-only, no Mathlib match)
- `lem-pc-brown-representability-right-adjoint` (statement-only, no Mathlib match)

Attachments: none.

WANTED: none.

The imported item had no proof split and only one Mathlib grep. I followed the actual proof of Stacks Tag 0A9E (Lemma 48.3.1), whose prerequisites are the direct-sum and compact-generation results for `D_QCoh`, preservation of direct sums by `Rf_*`, and Brown representability. I searched the DAG and blueprint before creating each prerequisite; no existing node stated those facts. The existing Mathlib leaf `lem-weil-pbc-qcqs-morphism-permanence` supplies the morphism hypothesis used in step 4.

## Review by C1

I read Tag 0A9E in `duality.tex` and the cited `perfect` and derived-category lemmas in the Stacks checkout. Step 1 uses the existing 01OY statement exactly to obtain quasi-separatedness from local Noetherianity; quasi-compactness is part of the item's Noetherian convention. Step 2 uses the new direct-sums statement exactly as quoted. Step 3 uses the new compact-generation statement exactly as quoted. Step 4 uses the existing qcqs permanence statement for the morphism and the new direct-image direct-sums statement; both hypotheses are present after step 1. Step 5 uses the new Brown criterion together with the three preceding categorical properties, and the resulting right adjoint is precisely the item's conclusion. I checked the edge case `f = id_X`, where the identity functor has an identity right adjoint. Each new node is statement-only, has a complete self-contained statement, a Stacks source, blueprint ancestry, and LeanSearch/Loogle/Mathlib-grep searches. I corrected the source of the proof from the imported placeholder to Tag 0A9E and added the missing search kinds and split metadata.
