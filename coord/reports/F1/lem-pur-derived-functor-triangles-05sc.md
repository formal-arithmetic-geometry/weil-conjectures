Files written:
- `dag/nodes/sec-smooth-purity/lem-pur-derived-functor-triangles-05sc.json` (item, split)
- `dag/nodes/sec-smooth-purity/lem-pur-triangle-morphism-category-05r9.json` (statement, unsplit; no Mathlib match)
- `dag/nodes/sec-smooth-purity/lem-pur-essential-constant-cofinal-0a1s.json` (statement, unsplit; no Mathlib match)
- `dag/nodes/sec-smooth-purity/lem-pur-filtered-colimit-exact-00db.json` (statement, Mathlib AB5 generalization)

Attachments: none.

WANTED: none; the Stacks source is represented by its online tag and the repository's imported node source path.

## Review by F1
I reread the item and the parent exactness node, then checked Stacks 05SC in the derived categories text together with 05R9, 0A1S, and 05PY in Categories. The returned version used arrows in the wrong direction: I changed Step 1 to denominators $X'\to X$ and $Y'\to Y$, Step 2 to the cofiltered category of incoming triangle morphisms and the initial projection to $S/Z$, and Step 3 to the cohomological functor $\operatorname{Hom}(-,W)$. The existing 05R9 auxiliary statement now says exactly cofilteredness and initiality over $S/X,S/Y,S/Z$; 0A1S now states initial restriction for pro-diagrams. I added the statement-only converse criterion node for Tag 05PY and cited its exact Hom-colimit hypothesis in Step 4. I checked the hypotheses used in each step against the MS2/MS6 clauses of the saturated triangulated localization definition, the 05SA value maps, the exact-colimit and five-lemma nodes, and the shift node. I also reran Mathlib searches for all three auxiliary nodes; only generic eventual-constancy or initiality APIs appeared, so none is a Mathlib leaf. The identity triangle and a constant pro-diagram satisfy the revised statements directly.

What was wrong in the imported item: its proof was empty, so the 05SC argument and its non-elementary filtered/cofinal ingredients were absent. No duplicate node was found for 05R9, 0A1S, or 00DB.

## Not duplicates
lem-pur-essential-constant-pro-criterion-05py vs def-pc-essentially-constant-ind-diagram: the existing node defines the filtered ind-diagram notion, while this node states the converse Hom-colimit criterion for a cofiltered pro-diagram.
lem-pur-essential-constant-pro-criterion-05py vs lem-pc-essentially-constant-ind-hom-colimit: the existing node proves the forward Hom-colimit formula for an ind-diagram, while this node proves the converse implication for a pro-diagram.

lem-pur-triangle-morphism-category-05r9 vs existing 05R9-tag nodes: no existing node states the filtered/cofinal category of morphisms of distinguished triangles.
lem-pur-essential-constant-cofinal-0a1s vs existing essentially-constant nodes: no existing node states invariance under cofinal restriction.

## Second reading by F1

Step 1: checked against Stacks Tag 05SC paragraphs 1--3 and Tag 05R9; the MS2 square completion and essential-constancy replacement are explicit. Verdict: repaired and sound.
Step 2: checked against Tag 05SC's category I paragraph and Tag 05R9; the filtered/cofinal reduction matches the source. Verdict: sound.
Step 3: checked against Tag 05SC's five-term Hom diagram, Algebra Tag 00DB, and the cited five-lemma node; filtered-colimit exactness and shift outer terms match. Verdict: sound.
Step 4: checked against Tag 05SC paragraphs 5--6 and Tags 0A1S/05SB; cofinal transfer now precedes definedness and inversion. Verdict: repaired and sound.
New node `lem-pur-triangle-morphism-category-05r9`: checked against Categories Tag 05R9 statement; self-contained and exact. Verdict: sound.
New node `lem-pur-essential-constant-cofinal-0a1s`: checked against Categories Tag 0A1S statement; hypotheses and conclusion match. Verdict: sound.

Changes: expanded Step 1's essential-constancy square adjustment, added its definition dependency and citation, and made Step 4 establish definedness via cofinality before using inversion.

Additional second-reading repairs: corrected the 05R9 source to `derived.tex`, where Tag 05R9 is `lemma-limit-triangles`, and made Step 4 state explicitly that cofinality identifies the value over `S/Z` with `C` before applying inversion to the chosen denominator.
