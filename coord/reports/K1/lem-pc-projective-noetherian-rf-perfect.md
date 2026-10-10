# Stage 1 report

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-projective-noetherian-rf-perfect.json`: split item.
- `dag/nodes/sec-picard-framework/lem-pc-affine-sections-flat-over-base.json`: one unsplit statement-only node; Mathlib searches found no exact match.
- `citations.json`: verbatim step citations.

## Attachments

None. The target id and its key notions were searched in both Lean source trees; no sorry-free declaration states the item.

## WANTED

None.

## Not duplicates

`lem-pc-affine-sections-flat-over-base` vs existing flatness nodes: those existing nodes concern flat morphisms, flat pullback, or stalk criteria, while this node states the affine algebra/module criterion from localized module flatness to global base flatness.
- `lem-pc-affine-sections-flat-over-base` vs `lem-sc-p1-localization-short-exact`: the existing node concerns exactness of a localization sequence, not flatness of a module over a base ring.
- `lem-pc-affine-sections-flat-over-base` vs `lem-weil-pbc-regular-local-maximal`: the existing node concerns regularity of a local ring, not module flatness.
- `lem-pc-affine-sections-flat-over-base` vs `lem-weil-pbc-localization-flat`: the existing node proves a localization ring map is flat, not the local criterion for an arbitrary module over an algebra.
- `lem-pc-affine-sections-flat-over-base` vs `lem-weil-pbc-localization-regular`: the existing node concerns regularity under localization, not module flatness.
- `lem-pc-affine-sections-flat-over-base` vs `lem-weil-pbc-flat-local-ring-maps`: the existing node concerns flat local ring homomorphisms, not an arbitrary module's flatness criterion.
- `lem-pc-affine-sections-flat-over-base` vs `lem-weil-pbc-flat-map-local-criterion`: the existing node treats flatness of the ring map itself; this node treats a B-module M over A.
- `lem-pc-affine-sections-flat-over-base` vs `lem-weil-pbc-regular-through-localization`: the existing node transports regularity through localization, not module flatness.
- `lem-pc-affine-sections-flat-over-base` vs `lem-weil-pbc-weakly-regular-sequence-localization-prime`: the existing node concerns weak regular sequences after localization, not flatness.
- `lem-pc-affine-sections-flat-over-base` vs `lem-weil-pbc-annihilator-localization-finite`: the existing node concerns annihilator localization for finite modules, not the arbitrary-module flatness criterion.
- `lem-pc-affine-sections-flat-over-base` vs `lem-weil-pbc-flat-over-localization`: the existing node compares flatness over a ring and its localization for a localized module, not all primes of an algebra.
- `lem-pc-affine-sections-flat-over-base` vs `lem-sc-affine-standard-cover-finite-free-local-fp-flat`: the existing node derives finite presentation and flatness from finite-free localizations, whereas this node assumes flat localizations and concludes flatness.

## Review by K1

I read the imported item and its blueprint proof, the existing Cech resolution node, the projective coherent-finiteness node, and the bounded-flat-complex perfectness node. Step 1 uses the Cech node only for its stated derived-direct-image computation. Step 2 uses the new node exactly for its conclusion that the affine section module is flat over the base; the remaining finite-direct-sum assertion is elementary. Step 3 uses the two cited existing statements exactly: finite cohomology and replacement by a bounded finite-projective complex. The local Noetherian, projective, coherent, and relative-flat hypotheses are the hypotheses used in the corresponding imported argument. I searched the whole DAG and blueprint before creating the new node, tested the criterion on $M=0$, $M=A$, and a localization $M=B=A_s$ (all satisfy the conclusion), and recorded all Mathlib searches, including LeanSearch unavailability. The item has no Lean attachment and remains a natural-language split.

## What was wrong

The imported second proof paragraph used the affine sections flatness implication without a cited node. I isolated that implication as a statement-only dependency; no other proof clause was moved into a new node.

## What could not be finished

The new criterion is unsplit because Mathlib searches did not find an exact declaration; it is intentionally left for a later stage-1 worker.

## Second reading by K1

- Item statement: checked against Stacks `perfect.tex`, Tag `0B91`, label `lemma-flat-proper-perfect-direct-image-general`, clause (2); locally Noetherian/projective/coherent/flat hypotheses and perfect derived direct image agree. Zero sheaf, a projective scheme over a field, and the empty scheme give the expected special cases.
- Step 1: checked against the Cech node statement and its finite affine-cover, separated, quasi-compact hypotheses; the cited node explicitly says the non-augmented Cech terms compute `Rf_*`, so the citation is sufficient.
- Step 2: checked against Stacks `algebra.tex`, Tag `00HT`, label `lemma-flat-localization`, part (6), and the new node; localization at every prime of the affine section algebra gives flatness over the corresponding base localization. The kernel argument in the step is the direct localization proof, and the finite direct-sum assertion is elementary. Tested $M=0$, $M=A$, and a field base (all conclusions hold), including the empty affine chart.
- Step 3: checked the exact statements of `lem-pc-projective-coherent-finiteness` (finite cohomology) and `lem-pc-noetherian-flat-complex-perfect` (bounded finite-projective representative); both citations state exactly what the step uses, and the local perfectness conclusion matches the item.
- New node `lem-pc-affine-sections-flat-over-base`: checked self-contained ring/algebra/module and prime-localization hypotheses, TeX escaping, and the exact Stacks Tag `00HT` source. It is strictly smaller than the item and is not a restatement. Mathlib searches were reviewed; no single exact declaration replaces the Stacks criterion.
- Repaired the new node's source from the blueprint proof to Stacks Tag `00HT` and removed the incorrect `def-weil-finitely-generated-module` dependency, since no finite-generation hypothesis is present.
