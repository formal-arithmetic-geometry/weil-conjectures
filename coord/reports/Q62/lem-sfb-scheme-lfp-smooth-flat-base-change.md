# Stage-1 report: lem-sfb-scheme-lfp-smooth-flat-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-lfp-smooth-flat-base-change.json: item, statement, split; no exact Mathlib match.
- citations.json: 14 step/node entries, with verbatim statements read from the existing DAG.
- report.md: worker's report and direct-delivery self-review.

No new nodes and no new Mathlib leaves. prepare.py is a sandbox-only preparation script, not part of the DAG delivery. The existing item had no sandbox copy, proof or report when this attempt began. Its inherited Mathlib searches are retained; searches.jsonl records this attempt's actual searches.

## Attachments

None. Searched the live WeilConjectures source for the exact blueprint id and for smoothLocus, smoothAt, SmoothAt, smoothness/flatness and base-change notions. No project declaration states the pointwise equivalence under just these hypotheses. Existing global smoothness descent, source descent, and flat-morphism fibre criteria do not attach this item. No compilation was run.

## WANTED

None. The source needed is present in literature/stacks-project/morphisms.tex. No SGA source is used.

## Findings and changes

The imported statement is correct, exactly case (2) of Tag 02V4, lemma-set-points-where-fibres-smooth; no statement or hypotheses changed. The empty proof is replaced with five steps. Smoothness ascent is obtained by applying existing case (1) to a smooth open. For reflection, first reflect flatness at the selected point, then identify the residue-field fibres and apply existing case (1) to the fibre morphism (flat because its base is a field). The pointwise smooth-fibre criterion finishes. This avoids creating a redundant scheme-field-extension smoothness node or redoing the affine translation already supplied by case (1).

Read the chapter and unit records and the latest blueprint proof at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, clause (3). The current clause (3) is an assembly through proper/open direct images. The item's inherited from.place records the older detailed supporting chain through alterations and moduli; this delivery supplies its stated scheme prerequisite, not a replacement route for the unit. blueprint_refs.py ancestor reports from.node = None for this imported supporting chain, and this maintainer-owned value is preserved. Searches blueprint_refs.py search 'smooth flat' and '02V4' returned no blueprint matches; the existing same_as = [] is retained.

Read both semantic search phrasings, LeanSearch, Loogle '"smoothLocus"', and both logged grep outputs. They find global smoothness stability, smooth-locus definitions and openness, and ring smoothness results; none directly gives the item's pointwise reflection. Mathlib searches were made only through msearch.py, and inherited records were not claimed as newly run. No new nodes need duplicate or Mathlib-leaf verification.

## Review by Q62

I read Tag 02V4's complete statement and proof in morphisms.tex, including its distinction between case (1), where f is flat, and case (2), where g is flat. I also read Tag 01V9, lemma-smooth-at-point, especially (1) iff (2), Tag 01VB, lemma-base-change-smooth, and Tag 047C, more-morphisms-lemma-flat-locus-base-change, in more-morphisms.tex. The latter's clause (2) has exactly pointwise flatness of g and the pullback, with no surjectivity hypothesis. The existing pointwise-flatness node is its structure-sheaf specialization. I read the latest blueprint proofs of lem-pc-flat-field and lem-pc-smooth-flat as well. There are no new nodes whose sources need separate review.

For step 1 I opened all three cited nodes: lem-pc-smooth-flat supplies flatness and local finite presentation of the chosen smooth neighbourhood, lem-sfb-scheme-flat-smooth-point-base-change states the equivalence for a flat lfp morphism and an arbitrary base map, and lem-weil-pbc-open-fibre-product identifies its pullback with an open neighbourhood of the chosen point. In particular I am using case (1)'s statement and not its internal affine construction. A smooth point provides a smooth neighbourhood by the item's own definition.

For step 2 lem-pc-smooth-flat supplies flatness on a smooth neighbourhood; def-weil-flat-morphism defines the needed condition on its stalk map. Open restriction leaves that stalk unchanged. I verified that clause (2) of lem-sfb-pointwise-flatness-base-change asks only that g be flat at t and the base change flat at z, exactly what is available. Clause (3) of lem-weil-pbc-qcqs-morphism-permanence supplies local finite presentation of the pullback; no qc or qs hypotheses from its other clauses enter the proof. I deliberately did not infer global flatness of f from flatness at u.

For step 3 def-pc-scheme-fibre gives unique points above z and u; lem-trf-smooth-at-point-fibre-criterion applies because f_T is lfp and flat at z. The latter node assumes local flatness and so it is not being used to deduce flatness from smoothness. lem-weil-pbc-fibre-of-base-change supplies both the cartesian fibre comparison and its compatibility with the projections. This compatibility, plus injectivity of the fibre projection on points, proves the comparison sends the selected point to the selected point; it is not merely an unspecified isomorphism.

For step 4 lem-pc-flat-field states flatness of every scheme over a field, and clause (3) of the permanence node gives local finite presentation of U_v over its residue field. Thus case (1) applies to this fibre even when f itself is not globally flat. Its arbitrary-base-map clause permits the induced residue-field morphism without any separability, finite degree or perfectness hypothesis. This is the same fibrewise smoothness comparison used in the first paragraph of Tag 02V4, factored through the existing case (1) node instead of duplicating Algebra Tag 02UQ and its affine/scheme comparison lemmas.

For step 5 the criterion's hypotheses are f lfp (original), flat at u (step 2), and its fibre smooth at w (step 4). Its conclusion is precisely smoothness on an open neighbourhood of u. I checked every step's uses against the cited node's statement, and citations.json quotes those statements verbatim. The off-unit pointwise criterion is declared as a generic tool in split_report.tool_uses; all other nonleaf proof tools are in this item's unit or are definitions/Mathlib leaves.

I checked B1-B10: no new statement-only or definition nodes, self-contained unchanged item statement, correct source labels/tags, literal TeX in the JSON, no unsupported Mathlib match or attachment, and filled blueprint search record. I checked C1-C8: all non-elementary inputs are cited, every step reads cited statements rather than their proofs, all proof uses equal proof_deps, and no dependence on this item is introduced through case (1) or the flatness criterion. I checked D1-D5: no relabelling or displacement into a new node, no circular use of case (2), and actual flatness/fibre assembly arguments are written. I checked E1-E7 against the exact hypotheses and objects; no correction or statement dispute was needed.

Edge cases: if U_T is empty the universal assertion is vacuous. A nonsurjective open base change is permitted because a point z is fixed and only its local flatness is used. A singular finite-type scheme over a field cannot become smooth at a point above its singular point merely through a residue-field extension; the case (1) input gives this without assuming perfectness. A morphism f nonflat elsewhere is allowed: only flatness at u is deduced. The map g may be flat without being lfp, and the proof never applies openness or an lfp theorem to g. All five proof steps are shorter than 2000 characters.

## Not duplicates

No new nodes. The existing lem-sfb-scheme-flat-smooth-point-base-change is case (1) of Tag 02V4, with f flat and arbitrary g; this item is case (2), with f only lfp and g flat. Neither statement subsumes the other. I reuse case (1) on a smooth neighbourhood and on the residue-field fibre, rather than making an equivalent new node.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own stage states. Required server dry run and push follow this report.
