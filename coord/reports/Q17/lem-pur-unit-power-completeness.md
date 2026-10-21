## Worker report

Item: lem-pur-unit-power-completeness. Group: Q17. Stage 1 only, direct delivery, 2026-10-21.

### Files written

- dag/nodes/sec-smooth-purity/lem-pur-unit-power-completeness.json: statement unchanged; five proof steps, explicit dependencies, actual augmentation-unit equation, source and blueprint provenance, status split. Existing searches retained and five searches actually run by Q17 appended.
- citations.json: one verbatim statement excerpt for every citation in every proof step.
- report.md: this report.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. All non-elementary inputs already have DAG nodes. No Lean was written, compiled or built.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, unit_power_completeness, unitPowerCompleteness, derived-completeness terminology and the principal-completion files. The project has derived completion for constant coefficients, but no declaration found states the arbitrary commutative ring-sheaf comparison and its specified augmented units. In particular the principal right-orthogonal criterion in CategoryTheory/DerivedCategory/Complete/Principal.lean assumes a regular generator; it does not attach to this item, which deliberately allows zero divisors and nilpotents.

## WANTED

None. All mathematical sources used are available in literature/stacks-project/algebraization.tex.

## Corrections and remaining work

The imported node was statement-only, so its source place referred to an explicit argument that had not yet been written. I supplied that argument. The statement is correct and is unchanged. Its definitions now also cite the existing section-localization, extended-Cech and actual completion-unit nodes. No omitted clause, false hypothesis or statement dispute was found. No unfinished part of this one-level split remains.

The nearest blueprint ancestor is lem-weil-scalar-extension-composition, through lem-weil-finite-free-completed-scalar-comparison. I read its current main-20261015 statement (order 1828), its existing DAG proof, the chapter record sec-smooth-purity and unit sk-def-sf-operations, and SETUP's three levels. This item supplies the below-unit integral-completion ingredient for finite coefficient extensions; it does not change the chapter or unit route. The current blueprint ancestor is a statement without a proof paragraph in that snapshot; the first-proof-paragraph provenance refers to the existing DAG split's integral-representative argument and is made explicit in split_report.blueprint.

## Searches and reuse

Searched all dag/nodes statements and source places for 099B, lemma-derived-completion, principal completeness, augmented localization, vanishing localizations and Cech reflector. Read the statements of each selected dependency. Existing general ringed-site facts suffice. Whole-blueprint searches with tools/blueprint_refs.py for “derived completion”, “localization”, “unit power”, “unit times” and “positive power” did not find an equivalent imported node. The positive-power hit det-sp-scalar-extension-functor concerns finite coefficient scalar-extension composition, not this local completeness assertion. No same_as entry is appropriate and no new node was created.

Q17 ran msearch.py five times: LeanFinder with the local-completeness phrasing; Loogle with IsLocalization.Away, Associated; Mathlib grep with derivedComplete|derivedCompletion|derived.*[Cc]omplet|[Cc]omplet.*[Cc]ech; LeanSearch with the first semantic phrasing; and LeanFinder again with the augmented-complex/reflector phrasing. Every service returned results, and I read them. Loogle returns IsLocalization.Away.of_associated and iff_of_associated, whose source I read at Mathlib/RingTheory/Localization/Away/Basic.lean, lines 123–145; these are ordinary ring facts about associated elements, not the sheaf-derived reflection statement or its augmentation. The semantic results concern module-sheaf units/generators or generic derived-category localization. Grep returns only CompletelyRegular.lean. These do not make the item a Mathlib leaf. The exact queries, returned names and verdicts are appended to mathlib_searches; the command log is searches.jsonl. Inherited searches were preserved, not claimed as newly executed.

## Not duplicates

No new nodes. In particular I reused the existing general vanishing-ideal, Cech/Koszul comparison and Koszul-reflector nodes instead of creating a principal-completion theorem, an ideal-closure lemma or a new localization-power node.

## Review by Q17

I read algebraization.tex, section Derived completion on a ringed site: the localization definition preceding lemma-map-twice-localize (0996), lemma-hom-from-Af (0997), lemma-ideal-of-elements-complete-wrt (0998), definition-derived-complete (0999), lemma-derived-completion (099B) including its displayed augmentation, and lemma-derived-completion-koszul (0A0E) with its dual-Koszul proof. There is no SGA input. The explicit unit-times-power ring calculation is expanded by me, so proof_origin.by is agent rather than claiming Stacks states the complete comparison verbatim. There are no new-node sources to review.

Step 1 uses the statement of def-weil-pbc-ringed-section-localization: it really defines the sheafification of the sectionwise localization and its canonical algebra map, including the slice version. The inverse of b in R[1/a] is u b^(e-1)/a; the inverse of a in R[1/b] is u^(-1)/b^e. The fraction formulas show that the maps preserve coefficients, are inverse and commute with restrictions, so sheafification preserves the inverse equations. This is the elementary algebra calculation needed here, not a new non-elementary lemma. Crucially e is positive and u is invertible on every restriction.

Step 2 uses derived internal Hom as an actual contravariant/covariant functor, exactly the functor clause in def-pur-derived-internal-hom. I also opened lem-weil-pbc-ringed-derived-complete-elements-ideal: its statement says the vanishing sections form a sheaf of ideals, including local generation. Thus it supplies the non-elementary passage from the chosen generator to every section of its generated ideal on every slice. I did not infer this from the definition of completeness or merely equality of principal localizations. The sheaf-of-ideals clause also handles coefficients that exist only locally; this was a necessary point to make explicit.

Step 3 uses the exact one-factor complex and augmentation defined by def-weil-pbc-ringed-extended-cech. Its only chain-map square is lambda composed with the a-localization map equals the b-localization map, already proved in step 1. Degree zero is literally identity; thus the augmentation equation is an equality of chain maps, not just an unidentified isomorphism in the derived category.

Step 4 uses the functor clause of def-pur-derived-internal-hom and the statement of def-weil-pbc-ringed-completion-unit, which defines the actual evaluation-at-one identification and precomposition by the augmentation. Contravariance determines the direction alpha:F_b to F_a. The equation alpha eta_b = eta_a follows by precomposing with epsilon_b phi = epsilon_a. Its inverse is the requested comparison F_a to F_b and carries the actual units in the requested direction. Naturality follows from the bifunctor on the derived category, so arbitrary roofs are covered. No unspecified isomorphism to a complete object is used.

Step 5 cites lem-weil-pbc-ringed-cech-koszul-dual-limit and lem-weil-pbc-ringed-koszul-completion-reflector, whose full statements I opened. The first supplies a natural comparison from RHom(C_c,N) to the strict derived Koszul tower and explicitly says it carries the augmentation unit to the degree-zero tensor unit. The second supplies completeness of that tower limit and bijectivity of composition with precisely that unit into complete targets. Both statements allow a general small ringed site, arbitrary unbounded N and arbitrary sections; neither assumes a regular generator or exact countable products. The two-term Koszul degrees (-1,0) and transition (c,1) agree in both statements. Transport of completeness and the Hom bijection through the specified isomorphism is formal. This verifies that the functors called reflections in the item actually have that property, instead of just comparing two endofunctors. I deliberately used these two general nodes rather than the completed-fiber-cech-comparison node, whose statement is restricted to completed coefficients on a scheme's pro-etale site and would not satisfy C4 here.

The three general statement tools in steps 2 and 5 are outside the item's unit. They are declared in split_report.tool_uses as general ringed-site tools: no statement in this unit supplies these general completion facts and they do not replace any step of the six-functor route. I have not set the maintainer-owned tool_uses field. I checked that none of these dependencies reaches the item through statement or proof dependencies, so these citations introduce no cycle.

Small cases checked: e=1 gives the usual unit-multiple localization; b=0 and nilpotent b give zero localizations and identity completion, with both completeness conditions holding for every N; invertible b gives identity differentials in C_c and zero reflection, so only the zero object is complete; the zero ring and N=0 satisfy the same formulas. Zero divisors cause no problem because the proof only inverts sections and never cancels them in the original ring. If e=0 the assertion fails, for example a=1 and b=0 over Z, which confirms why the stated positive-exponent hypothesis is necessary. A site without a terminal object is covered by compatible global section families and sectionwise formulas; no affine scheme, stalk conservativity or global sections exactness is used.

Against B–E: the statement remains self-contained, notions cite existing definitions, TeX is written once, and no new statement-only obligations or duplicate nodes are introduced. Every non-elementary input has a cited statement and a verbatim quote in citations.json. The proof does not move a clause to a new node or use the proof of a dependency instead of its statement. All five steps are below 2000 characters. The main repairs during self-review were to include the vanishing-ideal lemma for the “every f” clause, to write the direction of the contravariant comparison and its unit equation explicitly, and to use genuinely general ringed-site Koszul results for the reflection clause.
