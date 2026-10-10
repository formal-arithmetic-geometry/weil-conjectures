# Stage-1 report

Files written:

- `dag/nodes/sec-picard-framework/lem-pc-ringed-space-pointwise-truncation-limit.json` — split statement, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-ringed-space-rgamma-derived-limit.json` — statement-only child, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-ringed-space-derived-limit-stalk-injective.json` — statement-only child, no Mathlib match.
- `citations.json` — verbatim statement quotes for every cited node and step.

Attachments: none.

WANTED: none.

The item was not present in the Lean source. I read Stacks Project `cohomology.tex`, Tag 0D62 (`lemma-is-limit-per-point`) and its cited Tags 0D60 and 0D61. The imported item statement agrees with 0D62. I searched the whole DAG and blueprint for the two auxiliary statements; neither existed. The successive truncation triangle is already stated by `lem-pc-derived-lower-truncation-step-triangle`, so I cited it rather than creating a duplicate. Mathlib searches were run for the item and both new nodes with LeanFinder, Loogle, grep, and LeanSearch; no matching theorem was found, and LeanSearch was recorded as unavailable.

## Review by F1

I checked the parent statement against Tag 0D62 hypothesis by hypothesis: it introduces a ringed space, a derived object, a pointwise fundamental system and bound, standard lower truncations, and the derived inverse limit, exactly as the source. The first child is Tag 0D60 and states both the commutation of derived sections with derived limits and the displayed short exact sequence; the second is Tag 0D61 and states precisely its hypotheses and stalk-injectivity conclusion. Both children are self-contained and statement-only, with all non-elementary notions linked to existing definition nodes.

Step 1 uses only the standard truncation property and the derived-limit notation, and establishes the cohomology isomorphism for `n >= -m`. Step 2 spells out the source's choice of `n(x)` and checks all three integer inequalities against the pointwise vanishing hypothesis; this is elementary arithmetic. Step 3 cites the existing successive-truncation triangle and uses its long exact cohomology sequence to obtain eventual isomorphisms in degrees `m-1` and `m`. Step 4 cites the two new statements: eventual isomorphisms give the required `R^1 lim` vanishing and injections into the fixed stage, so the stalk criterion applies; combining this with Step 1 gives an isomorphism on every cohomology stalk and hence in the derived category. I tested the bound on `m<0`, `m=0`, and `m>0`; in each case `n(x)>=-m` and the three inequalities hold. The zero complex and a tower already constant in `n` give the expected immediate special cases.

## Second reading by F1

- Item statement: checked against Stacks cohomology.tex Tag 0D62, hypothesis by hypothesis; verdict agrees, including the non-canonical derived-limit lift and “every such morphism” conclusion.
- Step 1: checked against Tag 0D62 and derived.tex Tag 0H72; added the compatible-lift node because the derived-limit definition alone does not provide the map.
- Step 2: checked integer bounds against Tag 0D62; verdict correct for negative, zero, and positive m.
- Step 3: checked the successive truncation triangle and long exact sequence against Tag 0D62 and node lem-pc-derived-lower-truncation-step-triangle; verdict correct.
- Step 4: checked Tag 0D61, Tag 0D60, and the stalk argument; repaired it to quantify over every compatible lift, matching Tag 0D62.
- New node lem-pc-ringed-space-rgamma-derived-limit: checked against Tag 0D60; self-contained statement and recorded searches are valid.
- New node lem-pc-ringed-space-derived-limit-stalk-injective: checked against Tag 0D61; hypotheses and conclusion are exact and searches are recorded.
- New node lem-pc-ringed-space-truncation-derived-limit-compatible-map: checked against Tag 0H72; statement-only, self-contained, and no Mathlib match.

Changes: added the Tag 0H72 compatible-map node and citation; corrected the parent `created.item`; made Step 1 cite the lift explicitly; changed Step 4 to prove the stated claim for every compatible morphism.
- Removed the attempted Tag 0H72 child: it duplicates the parent’s explicit compatible-map clause; the construction is now written directly as an elementary Step 1 argument.
