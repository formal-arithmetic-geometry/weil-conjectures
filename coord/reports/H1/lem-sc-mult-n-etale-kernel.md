1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-mult-n-etale-kernel.json` (corrected statement and four proof steps).
- Four statement-only nodes: `lem-sc-hom-etale-locus-translation`, `lem-sc-finite-flat-unramified-tangent-criterion`, `lem-sc-group-addition-tangent-differential`, `lem-sc-mult-n-tangent-differential`.
- `citations.json`.

2. Attachments: none. The source declarations `AlgebraicGeometry.etale_torsionSubgroupScheme` and `AlgebraicGeometry.etale_npow_id` are sorry-free syntactically but rest on sorried declarations, so they are not attachable under the worker contract.

3. WANTED: none.

4. What was wrong in the imported node: the arbitrary-field constant-group clause was false, and the proof was circular and only restated Tag 0BFH. I removed the section-number citation `Lemma 39.9.9`, retaining Tag 0BFH, and split the argument into four actual steps. The new nodes isolate translation invariance, the finite-flat tangent criterion, the group-addition differential, and the differential of multiplication by d. Existing nodes supply finite flatness, tangent-map linearity, and etale base change. The Mathlib searches for each new node were run and found no exact theorem.

## Review by H1

 I checked the source declaration in `WeilConjectures/AlgebraicGeometry/AbelianVariety/Torsion.lean` lines 61-108 and the Stacks source for Tag 0BFH. Step 1 uses the new translation node, which states exactly that the etale locus of a homomorphism is translation invariant. Step 2 uses the existing finite-flat statement and the new tangent criterion; their hypotheses match the abelian variety and rational identity point. Step 3 uses the existing linearity node plus the two new differential statements, yielding scalar multiplication by d, injective because d is invertible in k. Step 4 uses the existing Tag 02GO base-change node and the finite-flat rank statement. I verified every citation quote against the cited node statements and recorded all eight entries in `citations.json`. Small cases `g=0` and `d=1` remain consistent. The removed `Lemma 39.9.9` section-number citation and the circular `lem-sc-ntorsion-etale` route are absent.

5. What I could not finish: none.

## Second reading by H1

- Item statement: checked against Stacks Tag 0BFH, Lemma 39.9.9 and the Lean declarations `etale_torsionSubgroupScheme` (Torsion.lean:61-79) and `etale_npow_id` (Torsion.lean:81-108); the stated implication, finite etale kernel, and rank clause agree. The source's nonzero hypothesis is only needed for its converse, while the dimension-zero case satisfies the stated implication directly.
- Step 1: checked that `lem-sc-mult-n-finite-flat` states finite flatness, locally free rank `d^{2g}`, and kernel order `d^{2g}` under exactly the item's hypotheses; Tag 0BFH supplies etaleness of multiplication, and base change to the identity supplies etaleness of the finite kernel. No uncited non-elementary fact is used.
- New node `lem-sc-mult-n-etale-kernel`: statement-only form, self-contained hypotheses and definition references, source tag and label, and no new node dependencies beyond the cited finite-flat node; the four recorded Mathlib searches were inspected and found no matching declaration.
- Edge cases checked: dimension-zero (the zero abelian variety), a field base, `d=1`, and the empty-scheme case (excluded by the abelian-variety hypothesis); all are consistent with the corrected statement. The old arbitrary-field constant-group assertion was false because finite etale torsion can have nontrivial Galois descent.

Changes made: retained the worker's corrected statement and finite-flat citation, removed the unsupported `lem-sc-fg-order-prime-etale` dependency and constant-group claim, and documented the source and edge-case checks here.
