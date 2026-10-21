## Worker report

Q84, stage 1, 2026-10-21. Item: lem-pod-isomorphism-scalar-comparison-agreement.

### Files written

- dag/nodes/sec-poincare-duality/lem-pod-isomorphism-scalar-comparison-agreement.json: split into four proof steps. Statement and statement dependencies retained verbatim. Added logged Mathlib searches, proof origin and split report, retaining the inherited searches and blueprint provenance.
- citations.json: nine entries, one for every step/node citation, each quoting the existing node statement verbatim.
- report.md: this report.

No new nodes; no Mathlib leaves. The supporting write_split.py and searches.jsonl are sandbox working records, not DAG delivery files.

### Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, scalar comparison names, and combinations of scalar, isomorphism, whole-system and quotient-augmentation. No declaration states the equality of the two completed pro-etale integral coefficient maps. SchemeIsoDerivedFunctorComparisons.lean was read: its schemeIso_derived_functor_comparisons concerns modules on the structure-sheaf ringed space and provides existence isomorphisms, so it does not attach this item. Ordinary module-object change-of-scalars and normalized-tower declarations likewise do not state this equality. No compiler or Lake tool was run.

### WANTED

None. The blueprint and relevant Stacks sources are present. The comparison of these two specified normalizations is an agent argument, not a claim that Stacks states this equality.

### What needed repair

The inherited node had no proof and only two inherited grep searches. Its statement is well-typed with the two named comparison constructions and needs no correction. The new proof shares the normalized whole-system realization coordinates before comparing the arrows. It does not identify arrows merely because their evaluations agree or because their objects are isomorphic.

### Unfinished work

None in this one-level split. Existing cited nodes retain their own downstream obligations. No supporting statement was created or duplicated.

## Sources and searches

Read the current blueprint chapter and unit (sec-poincare-duality and sk-lem-finite), the ancestor prop-weil-operations.proof.md, its first-sentence reference lem-fix-weil-operations.proof.md, and def-weil-derived-pullback-tensor-hom.md. The imported chapter/unit records are older than the current blueprint; this delivery preserves them and the item's assignment. The ancestor's first sentence delegates equivariant operation lifts to lem-fix-weil-operations; its pullback/inverse-automorphism squares are the place served here. This is a normalization tool below that route, not a change to the chapter or unit.

Read Stacks proetale.tex, Tag 099N, lemma-pushforward-Noetherian-case, including (2),(5) and proof: completed pullback is ordinary pullback followed by completion and is computed on the quotient tower. Read sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok and proof: a K-injective entire sequence computes total limit and its product-cone realization. Read derived.tex, Tag 08TC, definition-derived-limit and following warning about nonunique derived-limit objects. These support the construction context; the specified-map comparison uses the existing stronger DAG statements and is marked agent-written.

Blueprint searches ran for scalar comparison, scalar extension, whole-system and tensor-and-completion; DAG searches ran for the exact equality and whole-system/quotient-augmentation terms. The close existing normalization and realization lemmas were read rather than recreated. No new node means there are no new-versus-existing tag pairs requiring a Not duplicates entry.

Ran the required msearch.py commands as Q84 for this item, with LeanFinder (two distinct phrasings), Loogle, LeanSearch and grep, and read their results. Queries and results are retained exactly in searches.jsonl and copied with verdicts into mathlib_searches. LeanFinder first found scheme pullback tensor-congruence lemmas, then exact-functor derived-category localization lemmas. LeanSearch found ordinary cone/limit maps and scheme restriction/pullback isomorphisms. Loogle returned no hits. The two broad CategoryTheory grep queries returned no hits. A targeted grep located the candidate declarations, whose source types were read in Mathlib/AlgebraicGeometry/PullbackCarrier.lean:230 and Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:61. Neither has completed integral coefficients or the two specified maps. Thus no exact match or one-line specialization supplies this item. No query not run is recorded as a new search, and all services answered successfully.

## Review by Q84

I checked the split against delivery-errors B–E with the node statements and sources open. The important point is that the general normalized-scalar comparison lemma already compares maps in the derived category of entire quotient systems and identifies the canonical tensor-normalized comparison after realization. It is stronger than an existence statement. The alpha node explicitly identifies its cone-and-completion formula with that canonical comparison, so this split does not invent a new bridge theorem containing the item itself.

Step 1 uses the statement of lem-trf-effective-comparison-realization-models for simultaneous normalized primitive realizations, actual quotient transitions, and constructible-complete intermediate objects. It permits equality of the coefficient extensions, so setting the optional third field M=L is legitimate. def-trf-integral-comparison-sequence-systems supplies the actual system operations and their tensor-generator comparison; it is cited only for those definitions and formulas, not for a theorem about completion. lem-weil-specified-pullback-comparison-alpha supplies P,Q and the exact quotient/cone models. Thus C, A, B and the two word coordinates refer to the same schemes, coefficients and K, not merely isomorphic unrelated systems.

Step 2 uses the exact conjugation formula in the statement of lem-trf-counit-realization-substitution. Its domain requires normalized systems with complete constructible intermediates, supplied in Step 1, and its words include scalar/pullback comparisons. The statement of lem-trf-integral-pullback-comparison-realization defines lambda and mu using these whole-system counits and defines a=mu^{-1}lambda. Its lambda includes scalar association into the common target quotient system, while mu supplies the target word coordinate. The equation in this step is consequently its stated comparison written in the substitution theorem's coordinates. No information is borrowed from an unpublished proof construction or from an individual finite reduction.

Step 3 uses lem-pur-normalized-scalar-comparison-realization, whose statement fixes the same def-trf-integral-comparison-realization-models normalization and explicitly concludes that the canonical pullback scalar comparison is realization of kappa^D in those coordinates. The alpha node's final paragraph says its formula specifies the canonical tensor-association/strict-completion comparison, rather than an arbitrary isomorphism. I compared its displayed d_m with balanced scalar association and the formula defining the system comparison: inserting one and then multiplying the coefficients gives the displayed iota_m(b) pi_m(s) formula. Quotient transitions are actual maps in both constructions. The alpha node specifies that delta acts on both cone coordinates, and that chi has zero shifted coordinate; the realization-model node specifies the same counit and zero-shifted normalization. This checks map normalization, not just the scalar action on objects. I did not deduce equality of system arrows from equality of their evaluated arrows. All non-elementary localization/realization assertions in this step are precisely the conclusion of the normalized-scalar lemma, not an inline unproved descent argument.

Step 4 cancels the common invertible beta_B in the two equations. It is elementary category algebra, uses no further lemma, and proves the whole requested equality for each K. All cited statements were read; citations.json quotes their relevant statement text, not their proofs. The five off-unit statement citations are declared as generic tools in split_report.tool_uses, with their specific roles. Definition citations introduce common normalization and operations; neither substitutes a different unit route.

I checked hypotheses and small cases: the schemes need only the item's isomorphism and invertibility of ell, not properness, finite type or smoothness; all general realization tools admit these hypotheses. No flatness of A_E,n to A_L,n is used in the ramified case; computations are on K-flat models, as stated by the cited lemmas. No finite Tor-amplitude restriction is added. For E=L both constructions use multiplication/completeness and the equations reduce to the identity comparison. For g the identity, balanced association gives scalar completion with the same quotient unit. For K=0 or the empty scheme all involved maps are uniquely zero and the argument still applies. For shifted or unbounded K-flat representatives the scalar factor has degree zero and the displayed maps preserve degree; the cited whole-system localization supplies representative independence. There is no elementwise reconstruction or lim^1 uniqueness assumption.

Every non-elementary step is shorter than 2000 characters (863, 802 and 1461 at writing); the last elementary step is 323 characters. I found no hidden new lemma: model existence, substitution and tensor-normalized realization are existing general statements. No new unsplit statement, hollow definition, SGA citation, target change, repository edit, compiler invocation, or agent delegation is part of this delivery.

## Validation

Required dry run exited successfully: deliver.py Q84 lem-pod-isomorphism-scalar-comparison-agreement --no-push printed "OK (not pushed) deliver/Q84/lem-pod-isomorphism-scalar-comparison-agreement at 50cec284cbd: preflight passed". The server preflight includes check_dag.py and review_split.py. No local compiler or local forbidden validator was run. Final push follows this completed dry run.
