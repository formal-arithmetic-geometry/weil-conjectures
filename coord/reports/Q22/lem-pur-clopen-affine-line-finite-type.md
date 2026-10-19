## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-clopen-affine-line-finite-type.json`: existing statement split into six proof steps; statement and statement dependencies retained. Not an exact Mathlib leaf: separate generic restrictions and permanence results are needed.
- No new nodes and no new Mathlib leaves. `citations.json` contains a verbatim statement quotation for every node cited by every numbered proof step. `searches.jsonl` retains the five searches actually run for this item.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint id and for clopen, affine-space, finite-type and separatedness terminology. There is no declaration covering both clauses under precisely these hypotheses. Generic affine-space or noetherian results do not constitute an attachment. Upstream master is not used as finished-proof evidence.

## Wanted literature

None. All sources used are present under `literature/stacks-project/` and `literature/blueprint/`.

## Problems found and changes

The imported auxiliary statement is correct, but had no proof. It was extracted by NS from the parent invariance proof's Step 1 (retained DAG Step 3). I kept every hypothesis and both conclusions, including arbitrary finite rank, empty U and rank zero. The current main-20261015 parent statement and `.proof.md` agree with that purpose. There is no statement dispute and no unit-route departure. No unit or chapter file was changed.

The proof now checks quasi-compactness of the inclusion on every affine inverse image, rather than merely asserting that U is quasi-compact. Separatedness of the two structure morphisms is proved using the actual diagonal squares. The polynomial-ring argument explicitly uses finitely many variables. I corrected a draft citation to closed-immersion composition to Stacks 01QS after reading the tag table and the lemma; 01QQ is a different theorem.

## Unfinished work

No mathematical gap remains in this one-level split. Existing cited nodes retain their own proof/audit states. This is a DAG-only delivery; no Lean was written and no compiler, Lake command or build tool was run.

## Not duplicates

No new nodes were created. Whole-DAG title/statement searches and blueprint searches for `affine space`, `clopen`, and the diagonal/closed-immersion facts found the existing generic tools used below, not an existing blueprint theorem stating this combined auxiliary result. `blueprint_refs.py ancestor` confirms `prop-pur-a1-invariance`; `same_as` is empty. In particular the existing quasi-compact-open-immersion finite-type node gives one ingredient, not the whole item.

## Review by Q22

I read the worker brief, stage-1 contract, SETUP's three-level rules, delivery-errors B through E, GOAL and dag-sync, the chapter and unit records, the old parent proof and main-20261015 parent statement/proof. This item serves the clopen reduction of affine-line invariance; it does not replace that unit's sheaf-gluing route. Its statement is meaningful for every field, with no perfection, algebraic-closure, characteristic, nonemptiness or Noetherian assumption needed. There are no new statements to audit against literature.

For Step 1 I opened `def-weil-open-immersion`, `lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-closed-in-quasi-compact` and `def-weil-finite-type-morphism`. The first identifies the inverse image with U intersect V, the second states quasi-compactness of every affine scheme, the third gives quasi-compactness of a closed subset in the induced topology, and the fourth defines quasi-compact morphisms by these affine inverse images. The closed hypothesis is used exactly here, since U intersect V must be closed in V. I read Algebra 00E8 (`lemma-quasi-compact`, algebra.tex:3252) and Topology 005C (`lemma-closed-in-quasi-compact`, topology.tex:1662). No general quasi-compactness claim for arbitrary opens was substituted.

For Step 2 I opened `lem-weil-pbc-qc-open-immersion-finite-type` and `lem-sfb-finite-type-composition-base-change`. Their statements give exactly finite type of a quasi-compact open immersion and of a composite of two finite-type morphisms. Step 1 supplies the former's missing hypothesis; finite type of f is given. I read Morphisms 01T2 (`lemma-locally-finite-type-characterize`) and 01T3 (`lemma-composition-finite-type`).

For Step 3 I opened the open-immersion definition, fibre-product universal property, separatedness definition and `lem-weil-pbc-closed-immersion-base-change`. The last permits arbitrary base-change morphisms, with no flatness or smallness condition. The diagonal of U over S is the pullback of the diagonal of Y over S because two maps into the open subscheme with equal composites into Y are equal, including their structure maps. The step spells out this universal-property check instead of citing a definition for a permanence theorem. Given separatedness of f, its diagonal is indeed a closed immersion. I read Schemes 01KK (`definition-separated`) and the diagonal argument of 01KU (`lemma-separated-permanence`), and Morphisms 01QR (`lemma-base-change-closed-immersion`).

For Step 4 I opened `def-sbc-affine-space`, `pqf-def-affine-morphism`, the finite-type definition and `lem-weil-pbc-affine-morphism-permanence`. The affine-space definition actually supplies the polynomial chart on every affine base open; the affine-morphism definition therefore applies. Finitely many variables generate that algebra without another algebraic finiteness theorem. The permanence node explicitly supplies both quasi-compactness and separatedness of any affine morphism in clause (3), not merely a definition of affineness. I read Morphisms 01S6 (`definition-affine`), 01S7 (`lemma-affine-separated`) and the finite-type section 01T0. No nonempty chart or positive rank was assumed.

For Step 5 I reopened the fibre-product and separatedness definitions and both closed-immersion nodes. The base-change node gives the map X times_U X to X times_S X as a closed immersion once Step 3 supplies the closed diagonal of U. The cartesian square is checked by its pairs of maps, and all fibre products use their displayed bases. Step 4 supplies the closed diagonal of X over U. `lem-weil-pbc-closed-immersion-products` explicitly states that a composite of two closed immersions is a closed immersion; only that first clause is used. I read Schemes 01KU's proof of separated composition and Morphisms 01QS (`lemma-composition-closed-immersion`). These two short universal-property calculations do not hide a new comparison lemma.

For Step 6 the already-read composition node applies to p and the structure map of U, with finite type supplied in Steps 4 and 2. The rank-zero clause is explicitly in the affine-space definition. For empty U, there are no source points and the empty affine covers and empty diagonals satisfy the same definitions. I also tested U=Y, a proper clopen component of a disconnected Y, r=1, arbitrary r, and nonreduced finite-type Y: neither reducedness nor connectedness appears in the argument. Finiteness of r is essential for the polynomial generation, and is a stated hypothesis. The source is not wrong and no statement was weakened.

Every non-elementary fact in these steps is an existing cited node; all quotations in `citations.json` were generated from the actual statements read above. The elementary parts are intersections with a closed subset, finite polynomial generation, and the displayed fibre-product identifications. No step exceeds 2000 characters (the maximum is 746), and no new leaf or statement was introduced merely to restate a clause. The generic statement nodes used from other units are already Mathlib leaves, except closed-immersion composition whose slopmaster2 audit is closed; definitions are permitted notions. No off-route unresolved statement is used.

I ran LeanFinder with two distinct phrasings, Loogle, LeanSearch and the required Mathlib grep through msearch.py, and read their hits. They return generic local finite-type restriction, separated restriction, affine separatedness and finite affine-space local finite-presentation facts, not the combined item. The `isProper` and `IsFinite` hits impose stronger hypotheses and are not matches. I read the returned local finite-type and separated-restriction declarations in the local Mathlib source; I preserved the earlier NS searches and appended only my actual logged queries. There are zero fabricated searches and zero new nodes requiring a match record.
