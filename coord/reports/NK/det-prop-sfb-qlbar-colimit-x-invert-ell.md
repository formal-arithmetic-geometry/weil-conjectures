# Stage-1 report: det-prop-sfb-qlbar-colimit-x-invert-ell

## Files written

- `dag/nodes/sec-proetale-coefficients/det-prop-sfb-qlbar-colimit-x-invert-ell.json`: statement, split into five proof steps; no exact Mathlib match. No new nodes or Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every node cited at every step.

## Attachments

None. The exact blueprint id and its docstring tag have no hits in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or its Comparator tree. Searches for `padicSubfieldRingObj`, localization/inversion, and integer-colimit terminology do not give the item's isomorphism and flatness statement. The upstream master is reference material only; it supplies no basis for a finished attachment. No compiler was run.

## WANTED

None. The proof follows the current blueprint, with the existing general sheaf-module facts sourced to Stacks Tags 03DB and 03EP, not SGA.

## What was wrong or incomplete

The imported proof did not cite its finite-limit commutation or filtered-colimit exactness/tensor ingredients. The earlier sandbox attempt also quoted the left-adjoint assertion about `p^*`, rather than the clause about the actual composite `p_X^*`, and did not justify why an abelian-sheaf colimit is the required module colimit. The present split fixes these points and makes all transition maps explicit. The statement is byte-for-byte the imported statement; adding the existing site definition to statement dependencies imposes no additional hypothesis on X.

The shared snapshot has no `chapter` or `unit` fields on this newly imported item and no records `dag/chapters/sec-proetale-coefficients.json` or `dag/units/sk-prop-sfb-qlbar-colimit-x.json`. I left all maintainer-owned metadata untouched and read the current blueprint's chapter `_section.md`, unit `_section.md`, unit proof, and detailed item proof directly. The split realizes the unit's second isomorphism by its prescribed pointwise-denominator and pullback route.

## What could not be finished

Nothing mathematical remains at this one-level split. The new unsplit-node count is zero. Delivery is reserved for the fresh second reader, as required by the brief.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches for localization and inversion locate the larger comparison `sk-prop-sfb-qlbar-colimit-x`, which includes this isomorphism but also inverse limits, the algebraic-closure colimit and inverse-image compatibility. Citing it would be circular; it is not the same statement. Existing generic ingredients are reused directly: the filtered-colimit/finite-limit Mathlib leaf and the sheaf-module exactness/tensor lemma. No clause of this item was relabelled as a new node.

## Review by NK

I read the current blueprint chapter and the unit `sk-prop-sfb-qlbar-colimit-x/_section.md` and its proof, followed by the detailed statement and five-paragraph proof in `sk-prop-sfb-qlbar-colimit-x-invert-ell.md` and `.proof.md`. Their hypotheses are a finite extension E of Q_l and any scheme X. I retained the module colimit, its prescribed cocone, the ring isomorphism, invertibility, and flatness without adding Noetherian, quasi-compactness, characteristic, or finite-type assumptions. For the generic facts used in the last step I also read `literature/stacks-project/sites-modules.tex`, label `lemma-limits-colimits` (03DB), including its forgetful/filtered exactness statement, and label `lemma-tensor-commute-colimits` (03EP), part (2), which applies to sheaves on a site, not just presheaves or ordinary modules.

Step 1 cites `sk-def-sfb-condensed-ring` for the section formula C(S,T), subspace absolute value and definition O_E={|x|<=1}, and `def-sfb-integers-to-subfield-point` for the actual inclusion. These are the statements read, not an argument hidden in their proofs. I replaced the unexplained phrase “compact hence bounded” with the nested open cover |h(s)|<l^m and the finite-subcover argument. Continuity into O_E is subspace continuity, and injectivity is pointwise cancellation in the field. The common-index formula explicitly checks the colimit equivalence relation and its compatibility with restriction. These are elementary consequences of compactness and the given definitions, so they are a proof step, not new nodes.

Step 2 cites the coherent-topology clause of `sk-def-sfb-condensed-ring`, which really says coverings contain finite jointly surjective families. Its equalizer uses only the finite products of covering objects and their pairwise fibre products. I read the entire statement of the Mathlib leaf `lem-weil-pbc-filtered-colimits-commute-finite-limits`; it explicitly includes abelian groups, and the index N is small and filtered. Thus it gives exactly the needed finite-limit comparison. The point inclusion citation identifies the structure maps, and naturality from step 1 identifies the sheaf with underline E. No preservation of arbitrary infinite limits is asserted.

Step 3 cites the actual fourth clause of `sk-def-sfb-pullback-from-point`: the composite p_X^* is both a left adjoint and strong monoidal. I wrote the Hom-adjunction argument for its colimit preservation and the finite-biproduct argument for additivity rather than using an unstated black box. `def-sfb-integers-to-subfield` explicitly identifies phi and both pulled-back coefficient rings. The earlier attempt passed from abelian sheaves to modules without an argument. I considered the existing generic forgetful-colimit lemma, but it carries an additional sheafification hypothesis; instead I wrote the linearity check using `sk-def-sfb-sheaf-tensor`, whose statement explicitly says tensoring with either abelian sheaf preserves colimits. Equality of the two action maps is tested after each colimit injection. Thus the underlying universal factorization is module-linear, and the colimit is in the category the item specifies. This is the same source route, with its module-structure detail filled in.

Step 4 cites `def-sfb-integers-to-subfield` for the ring-object map and `sk-def-sfb-pullback-from-point` for its strong monoidal inverse image. The constant 1/l gives the inverse scalar on the point, and the two inverse identities persist under that functor. The localization's universal property is part of the item's definition of O_{E,X}[1/l]. The map on every term is l^{-m}phi; I checked its multiplication formula with denominator l^{m+n}, and its underlying module map is the isomorphism already proved. No assertion about objectwise colimits on non-quasi-compact X is needed.

Step 5 cites the small-skeleton clause of `def-weil-pbc-proetale-site` and the complete statement of `lem-pc-module-filtered-colimits-tensor`. Its hypotheses are a small site and a sheaf of commutative rings: the chosen skeleton and O_{E,X} meet them. Its tensor formula applies with both complexes concentrated in degree zero; all other total degrees vanish. The same node states exactness of filtered colimits. I checked that l tensor 1 becomes multiplication by l under O tensor M=M, so a short exact sequence gives a natural diagram of short exact sequences and exactness of its colimit proves flatness. This use is a generic tool, recorded in split_report.tool_uses, not a replacement for a unit step.

For delivery-errors B through E, there are no new statements whose source, Mathlib status, or duplicate status needs certification. I checked each citation by opening its complete node statement and copied that statement into citations.json (in particular the previous weak quotes for p_X^*, the topology, and the tensor formula were corrected). No source was used for more than its statement. Every non-elementary ingredient is now a cited node; no new node restates a conclusion of this item, and proof_deps is exactly the union of step uses. Small cases checked were S empty, S a point, E=Q_l, ramified E (powers of l remain cofinal denominator bounds, no identification of l with a uniformizer), X empty, and non-quasi-compact X (where sectionwise computation was used only on the point). None requires a statement correction.

All Mathlib queries are recorded from actual msearch.py logs with their exact tool and query text, including invalid Loogle patterns labelled as query failures, not successful absence results. Second phrasings searched both the compact-image denominator calculation and sheaf localization/flatness. I read `IsLocalization.flat` at Mathlib/RingTheory/Flat/Localization.lean:37: its arguments are ordinary commutative semirings and a submonoid, so it does not itself prove this pro-etale sheaf statement. The condensed colimit hits concern locally constant functions or generic categorical colimits, not the claimed coefficient isomorphism. The item is therefore a split, not a Mathlib leaf. No Lean file, live file, or tool was edited, and no agent was started.

## Second reading by NK

- Item statement: checked against the blueprint node `det-prop-sfb-qlbar-colimit-x-invert-ell`; the finite extension, arbitrary scheme, module colimit, localization ring structure, ring isomorphism, invertibility, and flatness clauses agree hypothesis by hypothesis.
- Step 1: checked against the blueprint paragraph `*On the point.*` and the statements of `sk-def-sfb-condensed-ring` and `def-sfb-integers-to-subfield-point`; the compact denominator bound, empty-set case, cocone factorization, and restriction compatibility are explicit and valid.
- Step 2: checked against `*The colimit is a sheaf.*`, the coherent finite-cover clause, and `lem-weil-pbc-filtered-colimits-commute-finite-limits`; the finite equalizer argument and identification with the condensed field have the needed hypotheses.
- Step 3: checked against `*Pullback.*` and the complete statements of `sk-def-sfb-pullback-from-point`, `def-sfb-integers-to-subfield`, and `sk-def-sfb-sheaf-tensor`; adjunction, additivity, monoidal transport, and module-linearity justify the module colimit.
- Step 4: checked against `*Ring structure.*` and the cited ring-map and strong-monoidal statements; the localization map, denominator formula, multiplication, and isomorphism comparison are accounted for.
- Step 5: checked against `*Flatness.*`, `def-weil-pbc-proetale-site`, and `lem-pc-module-filtered-colimits-tensor`; the small-site hypotheses, tensor-colimit formula, and exactness argument establish flatness without extra assumptions.
- New nodes: none; no B1–B7 or duplicate-node repair applies.

Changes made in this second reading:

- Verified that the imported item must retain maintainer-owned `blueprint.from: null`; its exact five-paragraph proof places remain recorded in `split_report.blueprint`.
- Added this independent second-reading audit; no mathematical statement or proof step required correction.
