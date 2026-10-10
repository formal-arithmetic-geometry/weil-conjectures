# Stage 1 report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-affine-perfect-colimit-descent.json` — item, split.
- `dag/nodes/sec-picard-framework/lem-pc-finite-projective-colimit-descent.json` — statement-only child, no Mathlib match.
- `citations.json` — verbatim step citations.

2. Attachments: none.

3. WANTED: none.

4. The item had no project Lean declaration and no existing DAG node stating finite-projective descent along a filtered colimit. The source is More on Algebra, Tag 0BC7. I retained the item statement and made the proof explicit: finite bounded range, simultaneous descent of terms, descent of matrix entries, eventual vanishing of the finitely many square relations, and assembly of the complex isomorphism. The new child is strictly smaller than the item and states only the one-module input.

## Not duplicates

`lem-pc-finite-projective-colimit-descent` vs `lem-pc-affine-perfect-colimit-descent`: the child descends one finite projective module, while the item descends a bounded complex and its differential data.

## Review by K1

I read the item source, More on Algebra Lemma 15.76.18 (Tag 0BC7), including the affine reduction to finite projective modules and the finite matrix relations. I searched the whole DAG and found no node for this one-module descent statement; the nearest existing nodes concern finite presentation, projective modules, and elementwise filtered-colimit behavior, but do not state projective descent. I also searched the Lean source for the item tag and terminology and found no declaration.

Step 1 is the finite bounded-complex unpacking from the source and is elementary. Step 2 uses the child node exactly for each finite projective term, with directedness supplying a common stage. Step 3 uses the existing elementwise colimit node for matrix entries and the existing base-change elementwise node for eventual vanishing of entries of the composites. Step 4 is the direct assembly of the termwise identifications into a complex isomorphism. The hypotheses checked are precisely a filtered ring system, its colimit, and a bounded complex with finite projective terms. Small cases such as a one-term complex and the zero complex reduce immediately to the child statement and the empty differential list.

Mathlib searches were run for the child with LeanFinder, Loogle, and source grep; they found only general finite-presentation/projectivity lemmas and no filtered-colimit descent theorem. The item’s imported searches were retained and its blueprint ancestor/place and split report were filled.

## Second reading by K1

- Item statement: checked against More on Algebra, Tag 0BC7 (label `more-algebra-lemma-colimit-perfect-complexes`), including the filtered-ring-colimit and bounded finite-projective-complex hypotheses; verdict: repaired to state an explicit existence index and cite every defining notion.
- Step 1: checked against the finite bounded-complex reduction in Tag 0BC7; verdict: elementary and correct.
- Step 2: checked against the finite-projective module descent part of Tag 0BC7 and the child statement; verdict: correct after simultaneous-stage clarification.
- Step 3: checked against the finite-projective Hom descent and finite relation argument in Tag 0BC7; verdict: repaired because finite projectives need not have bases, so entrywise matrix descent was invalid.
- Step 4: checked against the assembly conclusion of Tag 0BC7; verdict: elementary and correct.
- `lem-pc-finite-projective-colimit-descent`: checked as the one-module finite-projective input of Tag 0BC7, with its colimit and projective definitions cited; verdict: retained as a strict substatement.
- `lem-pc-finite-projective-map-colimit-descent`: checked as the fixed-model Hom descent input of Tag 0BC7; verdict: added as a strict substatement, with LeanFinder, Loogle, and grep searches recorded.

Changes made: corrected the item’s stale `created.item`; replaced the imprecise “after increasing the index” wording by explicit existence; added definition citations; added the fixed-model map-descent node; rewrote Step 3 to use finite generators and eventual vanishing rather than unjustified matrices; updated proof dependencies and verbatim citations accordingly.

## Not duplicates

`lem-pc-finite-projective-map-colimit-descent` vs `lem-pc-affine-perfect-colimit-descent`: the new node descends one map between already chosen finite-projective models, while the item descends an entire bounded complex, its terms, all differentials, and square-zero relations.
