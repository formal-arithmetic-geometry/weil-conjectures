Files written:
- `dag/nodes/sec-picard-framework/lem-sc-proper-flat-right-adjoint-restriction-open.json` (item, split)
- `dag/nodes/sec-picard-framework/lem-sc-right-adjoint-open-support-criterion.json` (statement, no Mathlib match)
- `dag/nodes/sec-picard-framework/lem-sc-proper-flat-right-adjoint-open-support.json` (statement, no Mathlib match)
- `dag/nodes/sec-picard-framework/lem-sc-proper-flat-right-adjoint-direct-sums.json` (statement, no Mathlib match)

Attachments: none.

WANTED: `literature/stacks-project/duality.tex`, Tags 0E4G, 0E4H, and 0E4J; the local literature checkout has no Stacks TeX source. I checked the authoritative Stacks HTML pages for these tags.

The item had no declaration in either Lean source checkout and no existing DAG or blueprint node stated Tags 0E4G, 0E4H, or the support criterion. The item statement already packages the two applications of Tag 0E4J part (2), one for f and one for its base change f'. I added three strictly smaller statement-only children for the exact prerequisites used by the source proof. The existing proper-base-change node supplies properness of f'; flatness and finite-presentation permanence are the standard base-change clauses in the morphism conventions.

## Review by H1

I read the target statement and its source, Stacks Tag 0E4J, and checked it against the parent Tag 0AAB proof. I also read the source material for every child: Tag 0E4G Lemma 48.4.3 gives the equivalence between support preservation and the restriction map; Tag 0E4G Lemma 48.4.4 gives support preservation for proper flat finitely presented f; and Tag 0E4H Lemma 48.12.1 gives direct-sum preservation of the right adjoint. In Step 1, the first child says exactly that the restriction map is an isomorphism iff the relevant supported complexes stay supported, and the direct-sum child supplies the source's passage from bounded-below to unbounded complexes. In Step 2, the proper-flat support child matches all hypotheses of f and gives the support condition, so the criterion applies. In Step 3, I verified that the same hypotheses hold after the cartesian base change; the existing proper-base-change node explicitly supplies properness, while flatness and finite presentation are stable under base change. I declared that existing node as an off-unit tool use. Repeating Step 2 for f' gives the second restriction isomorphism, and both maps arise from the same open-square adjunction construction, yielding compatibility of the base-change map. I tested identity base changes, empty complements, and V=Y: every displayed map reduces to an identity or the corresponding adjunction unit/counit. Mathlib searches were run with `msearch.py` for the item and each child; only generic sheaf adjunction/support declarations appeared, with no derived quasi-coherent theorem. The LeanSearch service was unavailable for the item, as recorded by the search log.

What I could not finish: no local copy of the Stacks TeX source was available, so the report records the requested WANTED line; the proof was checked against the official Stacks pages instead.

## Second reading by H1

- Item statement: checked against Stacks Tag 0E4J (Lemma 48.12.2) and its restriction map, with the two applications for f and f' verified hypothesis by hypothesis.
- Step 1: checked against Tag 0E4G (Lemma 48.4.3), including its bounded-below clauses and the direct-sum extension to unbounded complexes; the cited statements now say exactly this.
- Step 2: checked against Tag 0E4G (Lemma 48.4.4), case (1); support preservation is correctly stated for bounded-below complexes and Step 1 supplies the unbounded extension.
- Step 3: checked against Tag 0E4J (Lemma 48.12.2) and Tag 0AAB (Lemma 48.12.4); properness uses the cited base-change node, and the restriction/base-change naturality is written explicitly.
- Node lem-sc-right-adjoint-open-support-criterion: checked against Tag 0E4G, parts (1)--(3); its statement is self-contained, cites each imported notion, and distinguishes D_QCoh^+ from D_QCoh.
- Node lem-sc-proper-flat-right-adjoint-open-support: checked against Tag 0E4G, Lemma 48.4.4, case (1); all hypotheses and the bounded-below support conclusion agree.
- Node lem-sc-proper-flat-right-adjoint-direct-sums: checked against Tag 0E4H, Lemma 48.12.1; the direct-sum conclusion and proper-flat-finite-presentation hypotheses agree.
- Mathlib searches: reran the recorded semantic, Loogle, and grep searches; no exact derived quasi-coherent theorem was found.
- Small cases: identity base change, empty complement, V=Y, and zero complexes reduce to the identity restriction or zero support assertions.

Changes made: corrected the support criterion and support-preservation child statements from unbounded to bounded-below form, updated Step 1 and Step 2 to use the direct-sum extension, strengthened Step 3's naturality argument, and updated verbatim citation quotes accordingly.
