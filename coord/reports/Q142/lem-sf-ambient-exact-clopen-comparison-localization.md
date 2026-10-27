# Stage-1 delivery: lem-sf-ambient-exact-clopen-comparison-localization

## Files written

- `dag/nodes/sec-six-functors/lem-sf-ambient-exact-clopen-comparison-localization.json`: existing statement, now split into five proof steps. The statement, statement dependencies, source and blueprint ancestor are unchanged. No new nodes; zero new Mathlib leaves.
- `citations.json`: twelve verbatim statement quotations, one per step/node pair.

The sandbox contained only dispatcher marker files at entry. No earlier proof, report or search log was replaced. The imported Mathlib search records remain, with the four actual searches of this session appended.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for clopen/proper-open/localization notions. The finite-coefficient clopen idempotent declarations address only part of this statement. The etale ClopenTransfer/ProperOpenComparison files concern a different site/coefficient setting. None gives all the pro-etale sheaf and simultaneous semilinear-system clauses under these hypotheses. The read-only `lean/Sheaf/SixFunctors/SemilinearProperOpenMatePasting.lean` definitions jAdj, beta, pi, alpha and gamma corroborate the requested normalization; they are not claimed as finished attachments.

## WANTED

None. The literature needed for this assembly is available locally.

## Issues found and corrected

There was no proof to retain in the imported item. The source citation 0F7B constructs an etale proper/open comparison, not this ambient pro-etale/system localization theorem. I therefore explicitly marked this proof as agent-written and used 0F7B only as the motivating comparison normalization. The simultaneous operations, clopen decomposition and geometric restriction bijection are taken from existing DAG statements, not attributed to 0F7B. Stacks 07A7 fixes the transpose convention and 015F supplies exact-functor localization background.

No statement dispute was found. In particular the square need not be Cartesian: s can select a proper clopen part, so the proof does not assert that a_Q or Gamma_Q is invertible. The uniqueness assertion is proved in the abelian category; the derived comparison is proved using localization of natural transformations. I did not infer equality of derived system maps from evaluation.

## Unfinished work

None for this one-level split. The cited unsplit clopen-restriction node remains its own item. This delivery does not claim that its dependencies have already been proved in Lean.

## Searches and reuse

I searched the DAG for clopen, exact localization, open base change, extension by zero and localization of adjunctions, and ran blueprint_refs ancestor on the item and blueprint_refs search for clopen, exact localization, proper open and localization. The nearest blueprint ancestor remains fix-prop-projection-formula, with the inherited precise composition/refinement/coherence proof sentence. No other blueprint node states the whole item. Existing lem-sf-ambient-clopen-restriction-uniqueness, lem-sf-open-tensor-normalization, lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-localization-universal-property, lem-sfb-exact-derived-composition and def-weil-exact-derived-adjunction suffice, so introducing a new geometric localization lemma would duplicate or merely repackage them.

The actual searches are in searches.jsonl and copied into mathlib_searches: LeanFinder used the open-adjunction/clopen normalization wording; LeanSearch used the derived coefficient-system wording; Loogle searched CategoryTheory.Adjunction.localization; grep searched localization_unit_app|localization_counit_app|liftNatTrans in CategoryTheory. All services answered. The semantic hits do not state this geometric theorem. The Loogle and grep hits do provide the generic localization tools already represented in the DAG. I read Mathlib/CategoryTheory/Localization/Adjunction.lean lines 89-129 and Predicate.lean lines 278-350: the former gives the actual localized unit/counit and the latter natural-transformation descent, composition and equality. This is not a one-line Mathlib specialization of the whole item because the geometric clopen comparison and its coefficient-system realization still have to be identified.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs to justify.

## Review by Q142

I read Stacks more-etale.tex Tag 0F7B, label lemma-shriek-proper-and-open (statement and initial construction, lines 2460 onward), sites-cohomology.tex Tag 07A7, label remark-base-change (lines 4033-4058), derived.tex Tag 015F, label lemma-right-derived-exact-functor (lines 5884-5899), and the open adjunction construction in sites-modules.tex Tag 03DI, label lemma-extension-by-zero (lines 2058 onward), with the exactness input supplied by the cited node's 03DJ statement. I read the unit and chapter records and the current blueprint fix-prop-projection-formula proof. The inherited coherence sentence is realized by checking that the underived and derived clopen maps have exactly the same normalization. This is not a change of the chapter or unit route, and no SGA source is used.

For Step 1 I opened the whole statement of lem-sf-ambient-clopen-restriction-uniqueness. It supplies this exact non-Cartesian proper/open geometry, both coefficient categories, their exact product equivalence, the identity/zero projector and Hom(b_!F,k1_!G) = Hom(s^*F,G). The substitutions F=q^*M and G=r^*M satisfy its hypotheses. This yields existence and uniqueness of the underived normalized arrow; it does not require a stalk conservativity theorem or derived evaluation faithfulness. No new node hides that geometry.

For Step 2 I opened lem-coef-semilinear-derived-sections and lem-pur-site-restriction-module-adjunction-exact. The former states componentwise exactness and actual simultaneous inverse image/open-extension adjunctions for strict systems with arbitrary transitions; the latter states exactness and adjunction for module sheaves. Thus the functors being localized really are additive and exact in the relevant abelian categories. I read the entire statements of the exact-functor factorization and localization-universal-property nodes: they give all unbounded complexes as representatives and descent of transformations, composition and equality. The statement of lem-sfb-exact-derived-composition fixes the exact-composition isomorphism by its representative equation. The statement of def-weil-exact-derived-adjunction expressly specifies the localized original units and counits. No claim is taken from a proof rather than a statement.

For Step 3 I opened lem-sf-open-tensor-normalization. Its inverse-beta formula is precisely the open adjunct of the pulled-back unit followed by the inverse pullback compositor, and it explicitly includes ringed diagram topoi of arbitrary coefficient systems. I wrote out that adjunct as the unit/compositor/counit word. Localizing each of these three arrows, using Step 2, gives the specified derived inverse beta. Equality on all derived objects follows from clause (3) of the localization universal property, whose statement I checked; it does not require localization to be faithful on individual cochain morphisms. This is a direct formula substitution, so the step is elementary relative to the cited facts.

For Step 4 I checked def-weil-pbc-composite-adjunction's two-unit/two-counit formulas and composite Hom-bijection. Their localized words are the composite localized adjunction, so the final compositor has the requested normalization. The clopen projector is (1,0) on each degree of the two complexes; applying localization leaves precisely that product projection. The standard exact-composition comparison was already cited in Step 2. These two direct calculations identify every factor of a_Q, including the open compositor; no unproved comparison lemma is concealed by the word "transport".

For Step 5 I opened def-weil-pbc-adjunction-mate and checked all six functor types in the explicit substitution. Its unit-square-counit word has source J_i S_r and target S_p J_k1, exactly as required. I also opened lem-sf-proper-open-projection-mate: its displayed alpha is literally the same clopen composite, and its statement specifies gamma as its proper-adjunction mate. Its final paragraph expressly includes the simultaneous system normalization. I use these displayed definitions only, not its separate projection-formula identity. Hence this final step is a substitution in the specified normalization, not an application of a theorem that restates the item.

Small cases checked: U empty gives the zero map to zero; an empty W forces U empty; Cartesian square gives s=id and removes the clopen projector; all four maps identities give identity beta, projector and mate by the adjunction triangle identities; a nonempty complementary clopen component is killed, without any spurious invertibility conclusion. The construction allows unbounded complexes and noncartesian coefficient systems, since exact localization uses every complex and is performed before evaluation. All five steps are under 2000 characters, and each non-elementary input has a cited node with a verbatim statement quote. The generic off-unit system, module-open, open-normalization and exact-composition tools are declared in split_report.tool_uses; they supply generic calculus and do not replace any unit-level proof step.
