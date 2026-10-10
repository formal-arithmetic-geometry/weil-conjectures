Files written:

- `dag/nodes/sec-picard-framework/lem-pc-perfect-two-out-of-three.json` — statement, split proof, and review metadata.
- `citations.json` — verbatim citations for every proof-step dependency.

Attachments: none. The ring-level Lean lemma `DerivedCategory.isPerfect_obj₂_of_distTriang` is not an attachment because it concerns `D(ModuleCat R)` rather than the scheme-level `D(O_X)` statement.

WANTED: Stacks Project, `cohomology.tex`, Tag 08CR (lemma-two-out-of-three-perfect), for the item; that source is not present in this checkout.

No source statement was changed. The imported item had no proof and no exact project declaration. The affine mapping-cone argument is written directly in Step 2 rather than introduced as a clause-level node. Mathlib searches were run for the item; LeanSearch was unavailable and is recorded as unavailable rather than as a negative result.

## Review by F1

I read the item node, its ancestor reference to `lem-sc-finite-duality`, the scheme and perfect-complex definitions, and the existing `lem-pc-perfect-thick-closure` proof that cites this item. The source checkout contains `isPerfect_obj₂_of_distTriang` in `CategoryTheory/DerivedCategory/Perfect.lean`, but its objects are derived modules over a ring, so it does not state the scheme-level item and has not been attached. The Stacks source named by the item is absent, hence the explicit WANTED entry and agent proof origin.

Step 1 uses only the definition that perfectness is local and that affine restrictions of strictly perfect complexes are bounded finite-projective complexes; the common affine refinement and preservation under localization are elementary. Step 2 uses the definition's affine characterization and the new node's exact conclusion. The cone has terms given by finite direct sums of the two bounded finite-projective representatives, so the finite-projective claim is the stated affine input. Step 3 uses only the definition's local characterization to glue the affine conclusions. I checked that all hypotheses are retained on each affine restriction and that the triangle remains distinguished under restriction.

I searched the DAG and blueprint for existing mapping-cone/perfect-triangle nodes and found no reusable lower-level node; the only related existing node is the target's downstream thick-closure node, which cites this item and would create a cycle. The affine cone construction is small-case checked on zero complexes and identity triangles, where it gives a bounded finite-projective cone directly.

## Second reading by F1

- Item statement: checked against the imported Tag 08CR label and the definitions of scheme, derived category, and perfect complex; verdict: hypotheses and conclusion are retained, including the unrestricted choice of any two terms.
- Step 1: checked against [def-pc-perfect-complex] and [lem-pc-perfect-affine-bounded-projective]; verdict: the reduction is local and handles all three choices of the perfect pair on one affine cover.
- Step 2: checked against the affine bounded-projective statement and the standard mapping-cone construction; verdict: the three cyclic cases are written explicitly, with shifts and finite direct sums accounted for.
- Step 3: checked against [def-pc-perfect-complex]; verdict: the locally strictly perfect remaining term is correctly promoted to a global perfect object.
- New nodes: no new node is introduced; the existing affine characterization was searched in `dag/nodes` and cited rather than duplicated. Its zero-complex and identity-triangle cases were checked.
- Searches: the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch searches were retained and agree that no Mathlib scheme-level closure theorem is available.

Changes made: repaired `created.item` to this item, added the existing affine characterization to the proof dependencies and citations, and replaced the incomplete single-case cone argument with an explicit three-case rotated-triangle argument. The Stacks `.tex` source named by Tag 08CR is absent from this checkout, so the original WANTED notice remains.
