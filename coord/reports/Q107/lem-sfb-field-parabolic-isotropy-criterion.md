## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-field-parabolic-isotropy-criterion.json`: statement item, now split into four steps; not a Mathlib leaf.
- `citations.json`: verbatim statement quotations for every step-node citation.
- No new nodes; zero new Mathlib leaves. All helper statements already exist.

## Attachments

None. Searching the project Lean source for the exact blueprint tag and for parabolic, isotropy, and cocharacter found no declaration stating this item. The noncentral keyword only hit an unrelated Cech-face comment. No sorry declaration was treated as a completed proof.

## Wanted literature

None. The PDF `literature/milne-algebraic-groups_iAG2017.pdf` and the Stacks sources needed here are present and were read.

## Findings and changes

The imported statement is correct and was retained verbatim, including its noncentrality condition and its finite/imperfect-field scope. It initially had no proof. I supplied the coordinate-cocharacter argument, the proper parabolic construction, the reductivity contradiction, and the minimality argument. The last argument uses Noetherian closed supports rather than an additional dimension comparison. This obtains exactly the same minimal-parabolic conclusion as the suggested least-dimension choice.

I searched the whole DAG for parabolic, cocharacter, Milne 25.2/25.1/13.33 and the generic scheme inputs before using existing helpers. Whole-blueprint searches for parabolic, cocharacter, minimal parabolic, and noncentral split torus found no equivalent blueprint statement. The ancestor command returns `None`; the item's inherited creation chain already has a null nearest blueprint ancestor. I retained that null, the inherited via chain and the precise inherited from.place instead of inventing an ancestor. The latest direct-images proof is `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`; I read its (3). The item remains a supporting lemma in its inherited group-theoretic prerequisite chain, not a claim that the latest blueprint itself states rational-parabolic theory.

Five fresh logged Mathlib searches were run through msearch.py: LeanFinder in two phrasings, LeanSearch, Loogle, and grep. The returned matrix parabolic and modular-cusp statements concern elements of GL(2), not parabolic subgroup schemes; the Lie and root-system hits concern different objects; the abstract subgroup-lattice hits supply no algebraic geometry. All services answered. The item's earlier Q47 search records were preserved as historical records and the fresh query records were appended, with their exact query strings and actual summaries. No new node was needed, and no absent search was fabricated.

Generic tool uses are declared in split_report for projective implies proper, smooth fibres geometrically reduced, and uniqueness of the reduced induced closed subscheme. The affine Noetherian input is already a Mathlib leaf. The cocharacter-geometry node has the same unit as the item. None replaces a unit-level proof route. The cocharacter-geometry node's dependency closure was read to ensure it does not reach this item, preventing circular use of the rational-conjugacy argument.

## Not duplicates

No new nodes. In particular I reused `lem-sfb-reductive-cocharacter-parabolic-geometry` rather than creating another parabolic-construction node, `lem-wf-affine-noetherian-components` rather than a new minimal-parabolic lemma, and the existing smooth-reduced and reduced-induced-closed-subscheme results rather than variants of those statements.

## Review by Q107

I read Milne Proposition 25.2 on printed p.545, Theorem 25.1 on p.544, and Theorem 13.33(a)-(e) and its proof on pp.265-266. Proposition 25.2 requires a noncentral split torus; replacing that by nontrivial would be false for G=G_m. The item correctly retains noncentrality. The source explains why P(lambda)=G forces the normal unipotent part to vanish. My proof uses the existing semidirect-product statement to give that implication directly, and writes the scalar-extension descent on the defining ideal rather than invoking an unnamed descent theorem.

Step 1 is elementary: every point of the split torus is the product of its coordinate cocharacters on the same algebra. If all coordinate factors commuted with every G-point, their products would commute. The given test-algebra witness contradicts this. This is valid without finding any special k-rational torus element, so finite fields cause no problem. Rank zero cannot satisfy the hypothesis.

For step 2 I opened the full statement of `lem-sfb-reductive-cocharacter-parabolic-geometry`. It applies to any field and any k-cocharacter of a reductive group, not merely to a split reductive group or a regular cocharacter. Its unrestricted clauses supply smooth geometrically connected closed P_lambda, the exact fppf quotient convention, and a projective representing scheme. The maximal-torus/regularity hypotheses occur only in its final additional centralizer clause, which is not used. I also opened `lem-kun-projective-implies-proper` and `def-weil-proper-morphism`; their statements give properness and finite type respectively. I checked Stacks Tag 01WC, label lemma-locally-projective-proper in morphisms.tex, whose projective-space argument matches this use.

For step 3 the same cocharacter node explicitly states normality of U_lambda in P_lambda, split unipotence, the semidirect-product isomorphism and arbitrary-field-extension compatibility. Under P_lambda=G these are precisely the hypotheses of the reductivity condition after algebraic closure. Its Z_lambda is defined functorially using all algebra extensions, exactly the centrality needed to contradict step 1. Equality after scalar extension makes the defining ideal zero because tensoring vector spaces with a field extension is faithful; the basis argument is written in the step. I did not infer centrality only from rational points or from Lie algebras, which would not justify the stated all-algebra conclusion.

For step 4 I opened the full statements of `lem-wf-affine-noetherian-components`, `sbc-lem-smooth-geometrically-reduced` and `lem-weil-pbc-reduced-induced-closed-subscheme`. Finite-type affineness of G gives the exact finitely generated coordinate algebra required by the first. Its descending-chain statement gives a minimal support in the nonempty collection by the explicitly stated descent contradiction. Every smaller parabolic Q is still contained in P_lambda. Smoothness of P and Q, part of the item's definition of parabolic, gives reducedness over the field by the second cited statement; here the structural fibre is the whole scheme. I read Stacks Tag 056T, label lemma-smooth-geometrically-normal in varieties.tex. The third cited statement, specifically clause (3), gives equality of the ideal sheaves of two reduced closed immersions with the same support. I read its source Tag 01J3, label lemma-reduced-closed-subscheme in schemes.tex, including its affine radical-ideal uniqueness proof. Thus equal supports really give equal subgroup schemes. This addresses the difference between reduced subgroups and arbitrary nilpotent thickenings.

The edge checks are: a torus or a central positive-rank torus fails the noncentrality hypothesis; a rank-zero torus is excluded by the witness; for GL(2) a diagonal noncentral coordinate cocharacter gives a proper triangular parabolic; the all-test-algebra construction and geometric reductivity cover arbitrary characteristic and imperfect fields. Nonemptiness in the minimal-support choice comes from step 2, and properness of the resulting subgroup comes from its containment in the proper P_lambda. No Borel defined over k is assumed. The sources are Milne and Stacks, with no forbidden SGA route.

For B1-B10 there are no new statement-only nodes to audit; the item retains self-contained definitions, its statement dependencies, its searches, and its blueprint data. For C1-C4 every non-elementary input is a cited existing statement, with verbatim quotations in citations.json. Step 1 is the only purely elementary step. C5-C8 were checked by the whole-DAG/blueprint searches, the dependency-closure check, and explicit generic tool declarations. For D1-D5 no clause was relocated to a new node, and both the properness contradiction and the minimal-support argument are present in the item's own steps. For E1-E7 the preceding hypothesis-by-hypothesis checks explain the base field, reductivity, reducedness and subgroup-scheme equality. Each step is shorter than 2000 characters, and none conceals a comparison lemma. I corrected the step-2 source wording so quotient existence is attributed to Theorem 25.1 and the cited cocharacter statement, not to Theorem 13.33 alone.

## Unfinished work

No mathematical part of the stage-1 split remains. Required server dry run and delivery are performed after this report is written; their command output is the validation record.

## Dry-run repair

The first dry run required a longer quotation for projective implies proper (the selected phrase was under 40 characters). I replaced it with that node's whole statement; its mathematical use is unchanged.
