# Q20 — lem-pur-good-truncation-exact-normalization

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-good-truncation-exact-normalization.json`: statement, split; no complete Mathlib match. Eight proof steps, retaining the statement and all inherited metadata and searches.
- `citations.json`: one verbatim statement quotation for every node used by every proof step.
- `report.md`: this report. `searches.jsonl` is the search command's unedited log.

No new nodes and no new Mathlib leaves. The auxiliary `write_split.py` stays in the sandbox and is not a delivery file.

## Attachments

None. Searching `lean/WeilConjectures/` for the blueprint tag found no declaration. Searches for good truncation, truncation normalization, and single-complex/cohomology comparisons found component results, not a declaration proving every clause. In particular the bottom-unit normalization module concerns a specified resolution comparison, not this assertion for arbitrary abelian categories. No source declaration containing sorry was treated as a finished proof.

## WANTED

None. The sources needed are present.

## Corrections and scope

The imported statement is correct, including the zero category, and is retained verbatim. Its proof was empty. The source attribution already describes the combined compatibility theorem as agent-formulated: Stacks 0118 gives the truncation construction and 06XS(2) the single-object Hom calculation, not all the normalization and composition assertions. The supplied proof is therefore explicitly agent-origin. No SGA source is used.

I read the chapter and smooth-purity unit, the current main-20261015 blueprint's `cor-pur-dualizing-object-purity` (especially its final sentence), and the item's blueprint ancestry. This item supplies the abstract normalization required by the inherited degree-zero map-gluing route. It changes no geometric proof step or coefficient category. `def-kun-truncations` is declared as an off-unit tool in `split_report.tool_uses`; only its general abelian good-truncation definition and retained-cohomology clause are used. All remaining cited ingredients are existing Mathlib leaves.

## Searches and existing ingredients

I searched the entire DAG's statements and titles for fully faithful single embeddings, exact cohomology comparison, localization/natural transformation descent, truncations, and the cited tags; and used `tools/blueprint_refs.py ancestor` and `search` with truncation, degree zero, and normalization. No blueprint node states the whole present normalization theorem. The more general reusable ingredients already exist as:

- `lem-weil-pbc-derived-single-fully-faithful`;
- `lem-weil-pbc-exact-functor-complex-cohomology`;
- `lem-sp-exact-functor-preserves-homology`;
- `lem-weil-pbc-exact-functor-derived-factorization`;
- `lem-weil-pbc-localization-universal-property`.

The current Q20 msearch log has seven actual searches: LeanFinder twice with different phrasings; Loogle twice (joint truncLE/singleFunctor pattern, then truncLE); grep twice (truncation/homology/exact-single comparisons, then singleFunctorCompHomologyFunctorIso and existence of a single model); LeanSearch once. All succeeded. They return ingredients or unrelated truncation/right-derived-zero constructions, not a one-line specialization of the complete item. I retained the inherited searches and appended exactly the new tool/query texts. Read source includes Mathlib FullyFaithful.lean:30–66, ExactFunctor.lean:35–55 and 112–149, Embedding/CochainComplex.lean:57–71,280–288,422–424, DerivedCategory/TStructure.lean:189ff, ShortComplex/PreservesHomology.lean:777ff, and Localization/Predicate.lean:278ff. A blanket leaf claim would omit the explicit roof and its exact-functor/composition coherence.

## Not duplicates

No new nodes. The five general ingredients above are reused, rather than copied into new nodes or restated as the item's clauses.

## Review by Q20

I read Stacks `homology.tex`, section-truncations (0118), including its cochain formulas and both retained-cohomology assertions; `derived.tex`, lemma-negative-exts (06XS), especially part (2); `homology.tex`, lemma-exact-functor (010N), including its kernel argument; `derived.tex`, lemma-right-derived-exact-functor (015F); and `categories.tex`, lemma-properties-left-localization (04VG). I verified the tag/label pairs in `tags/tags`. For the natural-transformation enhancement of localization I read Mathlib Predicate.lean, because Stacks 04VG itself states only the functor property. That enhancement is explicitly in the existing localization node's statement.

Step 1 uses the full statements of `def-kun-truncations` and `def-weil-abstract-derived-category`: the former explicitly gives the kernel/cokernel construction and retained cohomology, the latter defines quasi-isomorphisms and their inversion. The map to H^0 is checked as an actual chain map: the quotient kills the incoming differential. Its effect on H^0 is the identity on the cycles/boundaries quotient, not an arbitrary scalar. This is a direct calculation from these definitions, so it is elementary. Both positive and negative vanishing hypotheses are used.

Step 2 uses exactly the bijection in `lem-weil-pbc-derived-single-fully-faithful` for an arbitrary abelian category with a derived category. Conjugation by the previously constructed roofs gives the Hom bijection, and applying H^0 identifies its inverse with H^0 itself. It does not assume naturality in advance. Step 3 then uses that injectivity, already proved, to compare any two transported roofs and to prove naturality for every derived morphism. It is not an appeal to representative choices being canonical. All targets of the injectivity applications are still concentrated in degree zero. These steps also give the unique-b clause.

Step 4 uses the complex-cohomology node's natural isomorphism and its explicit projection normalization, the exact-derived-factorization node's natural comparison with termwise application, and localization-universal-property part (2) to descend it. I checked both functors invert every quasi-isomorphism and are defined on the whole derived category. This establishes naturality for arbitrary derived morphisms, without falsely citing complex-level naturality alone. All degrees are used to prove preservation of the degree-zero subcategory. Finite limit preservation gives F(0) ≅ 0; there is no enough-injectives or boundedness assumption.

Step 5 uses preservation-of-homology clause (a), which actually supplies the preserved kernel isomorphism, not merely the definition of exactness. The complex-cohomology node actually supplies compatibility with the cycles-to-homology quotient. I wrote the two chain-map identities with their precise source and target, including the direction FH^0 → H^0F. Localization then cancels the truncation comparison. The degree-zero component of the second identity is explicitly q_(FC)t^0 = χ F(q_C); it is not an unsupported assertion of compatibility. All other components are zero. The exact-derived-factorization statement supplies the natural comparison used in passing these identities to D(F).

Step 6 checks the single-complex comparison on a morphism b, with F(b) in degree zero, and uses its termwise factorization to get naturality. The previously established naturalities then transport the equality along r:QC ≅ K, and cancellation of D(F)r gives the equality at K. No faithfulness of representatives or cohomology on arbitrary derived objects is assumed.

Step 7 uses the preserved kernel/image/quotient clauses of `lem-sp-exact-functor-preserves-homology`: I checked the comparison maps by composing with monic inclusions and epimorphic projections. The resulting identities for χ and σ are written with the correct composite GF and derived-composition direction. The cited localization statement includes uniqueness of lifts, composition preservation and equality detection, so it really licenses the passage from termwise identities to coherent derived comparisons. This is a generic uniqueness argument, not a new compatibility lemma hidden behind the word 'transport'.

Step 8 checks the zero category explicitly. I also tested complexes B[0], a shifted nonzero object (which fails the hypothesis unless the shift is zero), acyclic complexes (all maps become the unique maps between zero derived objects), exact identity and zero functors, and two composable exact functors. For B[0] the roof and its normalization are the canonical single-complex identities. The Hom proof concerns only degree-zero objects, so it makes no false global faithfulness claim about H^0. No new statement needs small-case repair.

Against delivery-errors B–E: every citation was read as a statement rather than borrowed from a proof; every non-elementary tool is an existing cited node; the elementary steps are explicit quotient, conjugation, uniqueness or cancellation calculations. No new unsplit statement, duplicate, clause-restatement node, source section-number citation, or unavailable-service no-match was introduced. None of the eight steps exceeds 2000 characters. No cited node depends back on this item; server checks will confirm the full graph. `citations.json` contains actual verbatim text, including the clauses used. No repository, launcher, Lean source or compiler was modified or invoked.

## Unfinished work

None in the mathematical split. The delivery remains subject to the maintainer's independent review.

## Dry-run repair

The first preflight rejected the phrase “the item's” in Step 3 as non-self-contained wording. I replaced it by “the asserted”; the objects and hypotheses were already introduced in the node. No mathematical statement or argument changed.
