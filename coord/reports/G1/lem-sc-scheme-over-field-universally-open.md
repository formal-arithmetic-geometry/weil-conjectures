# Stage-1 worker report

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-scheme-over-field-universally-open.json`: split item.
- `dag/nodes/sec-picard-framework/lem-sc-open-map-local-on-source-target.json`: statement-only locality node; Mathlib search found no matching declaration.
- `dag/nodes/sec-picard-framework/lem-sc-affine-tensor-spectrum-open.json`: Mathlib leaf, exact match `PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field` in `Mathlib/RingTheory/Spectrum/Prime/Chevalley.lean:70`.
- `citations.json`: verbatim node-statement quotes for each cited proof step.

## Attachments

The slopmaster2 source contains `universallyOpen_of_locallyOfFiniteType_spec_field` in `WeilConjectures/AlgebraicGeometry/Hilbert/Curve.lean:1037`, but it requires `[LocallyOfFiniteType g]` and therefore does not state this item's arbitrary-scheme claim. No attachment was made.

## WANTED

The Stacks checkout is not present in this clone. The proof was checked against the online text of Morphisms Lemma 0383 (Tag 0383) and Algebra Lemma 037G (Tag 037G), while retaining the repository's recorded source path.

## Review by G1

I read the item's node and the unit/chapter records, then checked the source statement against Tag 0383: for every field $K$ and scheme $X/K$, every base change to a $K$-scheme $S$ is open. I also checked the exact slopmaster2 declaration and rejected attachment because its local-finite-type hypothesis is stronger than the item.

Step 1 follows the first sentence of the Tag 0383 proof. It cites `lem-sc-open-map-local-on-source-target`; that node's statement explicitly supplies the affine-cover locality needed to reduce both source and target. Step 2 identifies the affine fibre product with `Spec(A ⊗_K B)` and cites `lem-sc-affine-tensor-spectrum-open`, whose statement explicitly gives openness of the map induced by `B → A ⊗_K B`. Step 3 only quantifies the argument over all base changes and unfolds universal openness, so it is elementary. The `citations.json` quotes are copied verbatim from those two node statements.

For the new locality node I searched the whole DAG and blueprint before creation and ran LeanFinder, Loogle, and Mathlib grep; the hits concerned affine-local ring-hom properties, not `IsOpenMap`, so it remains statement-only. For the affine node I searched the DAG and blueprint and ran all three required Mathlib searches; LeanFinder, Loogle, and grep all found the exact Mathlib declaration at line 70, so it is marked `mathlib`. I tested the statement on $A=K$ (identity projection), $A=K[t]$ (polynomial projection), and $B=0$ (empty spectrum), all consistent with the claimed open-map theorem.

The item's existing maintainer fields and source metadata were preserved; only split-owned proof, dependency, search, blueprint-place, status, and split-report fields were changed.
