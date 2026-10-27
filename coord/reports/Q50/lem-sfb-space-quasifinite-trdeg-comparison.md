# Q50 stage-1 delivery: lem-sfb-space-quasifinite-trdeg-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-quasifinite-trdeg-comparison.json`: statement, split using existing scheme lemmas and the Mathlib transcendence-degree tower leaf; no Mathlib match for the entire chart assertion.
- `citations.json`: one verbatim statement quotation for each cited node in each proof step.
- `searches.jsonl`: actual search command results, appended by msearch.py.
- `report.md`: this report.

Zero new nodes; zero new Mathlib leaves. The existing Mathlib leaf lem-kun-transcendence-degree-tower is reused.

## Attachments

None. Searches for the exact blueprint tag and for quasi-finiteness/transcendence terminology in the live WeilConjectures source found no project declaration giving the whole item. The source's scheme quasi-finiteness predicates and partial field results are not attachments to an assertion about every scheme chart of an algebraic space.

## WANTED

None. All proof sources used are present in literature/stacks-project/.

## Statement corrected

STATEMENT-DISPUTED: the imported wording did not explicitly require g to be a morphism over k. With the independently specified k-structures on E and Y, its unrestricted reading is false. Let k = Q(t_0,t_1,...) with algebraically independent variables, L = k(u), E = Spec L and Y = Spec k, both with their ordinary k-structures. The field isomorphism phi:k -> L given by phi(t_0)=u and phi(t_{i+1})=t_i induces an isomorphism g:E -> Y of schemes, hence a locally quasi-finite map. Every etale chart composed with this isomorphism is locally quasi-finite. For the identity chart of E, however, trdeg_k L = 1 while trdeg_k k = 0. This g is not over k.

The corrected statement says that g is a morphism over k. Stacks 06RX explicitly considers composable morphisms of algebraic spaces over the same S; its specialization here uses S = Spec k. This clarification restores that source hypothesis and makes the specified residue-field k-structures compatible. No finite-type, quasi-compactness, separation, or surjectivity hypothesis has been added. The item's JSON also contained doubled literal TeX backslashes; these have been normalized to single TeX backslashes.

The sole live dependent node is lem-sfb-dm-field-etale-chart-quasifinite. Its fourth step applies this item to the two projections R = A x_Z A -> A over k. Both projections are over k by the fibre-product construction. The corrected hypothesis therefore holds in both uses. The dependency is not edited.

## Proof and sources

I read Stacks spaces-morphisms.tex, label lemma-compare-tr-deg, Tag 06RX, including its scheme-chart proof and the explanation after definition-dimension-fibre. I read morphisms.tex, labels lemma-residue-field-quasi-finite (01TG) and lemma-quasi-finite-at-point-characterize (01TH), including the first paragraph proving (1) implies (2). I read fields.tex, label lemma-transcendence-degree-tower (030H). The proof follows 06RX: reduce to the scheme chart, obtain a finite extension of residue fields, and remove that algebraic extension from the transcendence-degree calculation. The extra isolated-point step lets the proof reuse the precise existing DAG statement of residue finiteness rather than create another 01TG node.

The inherited chapter/unit and blueprint provenance are retained. I read the recorded chapter and unit, then the current latest blueprint unit and sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). The item's inherited provenance is an auxiliary input to the alteration/moduli branch of that paragraph, specifically the 06UC discrete-stack argument. The ancestor command reports None, so I did not invent a machine-resolvable blueprint ancestor. Whole-blueprint searches for quasi-finite transcendence-degree comparison / 06RX and for transcendence degree found no equivalent imported statement. No unit or chapter file is changed.

## Mathlib searches

The item retains Q49's prior searches as history and adds only searches actually run for Q50 with msearch.py. I read all returned hits. The first LeanFinder query concerned every etale chart of a locally quasi-finite algebraic space; the second asked the scheme residue-finiteness formulation. LeanSearch returned Algebra.instFiniteResidueFieldOfQuasiFiniteAt and scheme/ring quasi-finiteness components. Loogle with `"LocallyQuasiFinite", "trdeg"` returned no hits. The grep commands searched the scheme quasi-finiteness file and the AlgebraicGeometry directory. The directory query returned zero hits; it is not taken as independent evidence that the component theory is absent. The single-file wrapper prints line numbers as file names, which the recorded result explains.

I read the actual Mathlib scheme QuasiFinite.lean definition and its docstring: Mathlib's LocallyQuasiFinite does not impose local finite type, so it is not silently identified with the Stacks predicate. RingTheory/QuasiFinite/Basic.lean:427-438 provides finite residue fields at quasi-finite primes. TranscendenceBasis.lean:537-550 gives the cardinal-lift tower formula and Transcendental.lean:89-94 gives the zero-degree/algebraic equivalence. These component results do not make the entire algebraic-space chart assertion a one-line Mathlib specialization. The latter two field results are already represented by the cited Mathlib leaf.

## Not duplicates

No new nodes are proposed. Whole-DAG searches by Tags 06RX, 01TG/01TH and the terms residue finiteness, quasi-finite isolated fibre, and transcendence-degree tower found the existing nodes reused below.

## Review by Q50

I checked delivery-errors B through E against the statement, each proof step, and the source passages. There are no statement-only child nodes whose completeness or duplication could be in doubt; the item contains the argument rather than moving any clause into a new node.

Step 1 uses the statement of pqf-def-quasifinite for the pointwise meaning of local quasi-finiteness and lem-weil-pbc-lqf-locally-finite-type for the local finite type conclusion. The former genuinely includes the Stacks finite-type convention, and the latter states exactly the implication used. The chartwise assumption of this item gives that predicate for f = g composed with c directly. I did not invoke an unrecorded theorem that an arbitrary algebraic-space map is representable, or require that this chart cover E.

Step 2 uses lem-weil-pbc-quasi-finite-at-point-isolated and lem-weil-pbc-isolated-fibre-point-residue-finite. I opened both files and read their statements. The first requires local finite type, already proved in step 1, and pointwise quasi-finiteness, obtained by unfolding the same predicate. It gives isolation in the scheme fibre, precisely the hypothesis of the second. The second gives a finite extension for the residue fields of the original schemes W and Y, so there is no unproved replacement of a fibre residue field by a different field. Its local finite type requirement holds as well. Neither node requires the whole fibre to be finite.

Step 3 uses def-weil-residue-field, def-pc-field-extension, and lem-kun-transcendence-degree-tower. The definition statement supplies the induced residue-field map, and the field-extension statement supplies injectivity, so the tower lemma applies to actual embeddings. Compatibility of the k-structure is checked using composition of stalk maps and quotient maps; this is the reason for correcting the missing over-k wording. I wrote out the finite-dimensional linear-dependence argument giving algebraicity: every element a has n+1 powers in an n-dimensional space, and nonzero coefficients form a nonzero vanishing polynomial. This is a few-line elementary argument, not a concealed new lemma. Both clauses of the tower node are explicitly present in its statement: additivity and the equivalence between zero relative degree and algebraicity. The calculation uses cardinal addition, so no finiteness of absolute transcendence degree is smuggled in.

Step 4 is elementary: the two values equal the same fixed right-hand side. Empty charts and points with no lift give vacuous universal quantifiers. Non-surjective charts cause no issue because the proof is pointwise. Purely inseparable finite residue extensions satisfy the same linear-dependence argument; no separability or perfectness assumption occurs. The identity map and a finite field extension give the expected equalities. These tests also confirm that quasi-compactness and separation are not needed. Every non-elementary step cites its actual input nodes, all quotes in citations.json are copied verbatim from their statement fields, and no step exceeds 2000 characters (the complete assembly proof is under 3000 characters).

The three generic scheme facts from the proper-base-change unit are declared in split_report.tool_uses. They implement exactly the scheme residue-field input that 06RX calls for; they do not replace the enclosing constructibility route. The field tower node is already Mathlib. No cited node is a new restatement of this item's conclusion, and no item/new-node cycle is introduced.

## Unfinished work

None within stage 1. The cited existing nodes remain their respective owners' work. No Lean was written, compiled, or built; no repository or launcher file was edited.
