## Worker report

Files written:
- `dag/nodes/sec-purity-real-sheaves/lem-a1-surjective-chart-base-open-factorization.json`: statement unchanged; complete five-step split; no new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each node cited by each proof step.
- `report.md`: this report. Search tooling maintains `searches.jsonl`.

Attachments: none. Project-source searches for the exact blueprint id, surjective-chart/base-open name variants, and the representable-surjective notion found no declaration stating every clause of this item. Scheme-only facts are not attachments for this algebraic-space assertion.

WANTED: none. All source passages used are present locally.

The live item was unsplit, with statement dependencies and earlier Mathlib search records but no proof. There was no previous sandbox item/report to continue and no item-specific repair record. I retained the statement, provenance, earlier search records, chapter and unit. No imported statement dispute was found. No Lean was written or compiled.

## Sources and existing nodes

I read the fixed chapter `sec-purity-real-sheaves` and unit `sk-p-real-rankin`, including its first-step use of H_c^0 vanishing, and the three levels in SETUP.md. This item is an auxiliary step beneath `lem-a1-affine-hc0`, through the existing schemehood and affine-atlas chain; it does not replace the unit route. The current `main-20261015` blueprint file for that ancestor contains only its vanishing statement, so I have not invented a quotation from an absent blueprint proof. Its existing auxiliary source is Stacks Tag 03FY, `spaces-properties.tex`, label `lemma-union-of-quasi-compact`, whose final proof sentence concludes that the base-open factorization follows from the surjectivity of U_i -> X_i. I read that sentence and the surrounding affine-atlas construction. The present proof expands that inference and checks that affineness and etaleness play no role in it. The expansion is marked agent-written to distinguish the detailed generalized argument from the source's terse sentence.

For scheme tests I read `def-trf-algebraic-space` in full, Stacks `spaces.tex` Tag 025Y (`definition-algebraic-space`), and Tag 025V (`definition-relative-representable-property`). Representable surjectivity means surjectivity of every representing scheme projection, not objectwise surjectivity of sections. For open factorization I read `lem-weil-pbc-morphism-factors-through-open-subscheme` in full and its source `schemes.tex` Tag 01HI (`lemma-restrict-map-to-opens`), including the paragraph immediately following it, and checked Tag 01IK (`lemma-open-subspace-scheme`). I also read `def-weil-open-immersion`, `def-pc-scheme`, and `def-weil-size-convention` against the notions in the unchanged statement.

The only non-elementary fact used in the argument is the existing Mathlib leaf `lem-weil-pbc-morphism-factors-through-open-subscheme`, which supplies existence AND uniqueness for scheme morphisms whose underlying image lies in an open. Its exact declarations `IsOpenImmersion.lift`, `lift_fac`, `lift_uniq` were read in Mathlib/AlgebraicGeometry/OpenImmersion.lean, lines 701-713. No extra cancellation or general descent theorem is tacitly assumed. This Mathlib tool is allowed across units; the algebraic-space definition is a definition, so it also introduces no off-route theorem.

## Searches and reuse

I searched the whole DAG for the source tag 03FY and for open-factorization and surjective-scheme-test concepts. I read the statements of the same-unit `lem-a1-space-open-factor-scheme-tests` and `lem-a1-space-affine-atlas-open-cover` as well. The former is a more elaborate point-topology/open-subspace theorem and would require additional input identifying the relevant point images; the latter depends on the current item and cannot be cited back. Neither is needed for the direct scheme-test argument. No new node was created. Whole imported-blueprint searches were `python3 tools/blueprint_refs.py search 'open factor'` (one unrelated exchanges node) and `... search '03FY'` (none). The ancestor command identified `lem-a1-affine-hc0`. Consequently `same_as` is empty, and the existing precise `from.place` and via-chain are retained.

Fresh Q44 searches were run only through the prescribed msearch.py command: LeanFinder in two distinct natural-language phrasings, LeanSearch, Loogle for algebraic spaces/open immersions, and a Mathlib grep. The exact queries and returned logs are in the item's appended `mathlib_searches` and `searches.jsonl`. All services answered. LeanSearch and LeanFinder returned scheme cover, underlying-map image and scheme-local-representability declarations; Loogle returned no hits and grep returned the scheme immersion file. I read the relevant scheme source facts and their types: none states the item's algebraic-space assertion or is its one-line specialization. General scheme image equality under a surjection is elementary here and is written as a pointwise step, rather than turned into a new node.

## Not duplicates

No new nodes. The existing open-factorization leaf is reused rather than duplicated.

## Review by Q44

I checked the split against delivery-errors B through E with the item, the cited node statements and the Stacks passages open. B1-B9 cause no new-node obligations because the proof creates zero nodes; the unchanged statement already introduces S, U, Y, q, W, the scheme-test convention and size bounds. The two needed notions/results are cited as existing nodes, the source has tags and TeX labels, all formulas use single TeX escaping, and the recorded searches are actual tool invocations. B10 was checked by searching the live project Lean, not treating a Mathlib declaration or a merely related project theorem as an attachment.

Step 1 uses exactly the statement of `def-trf-algebraic-space`: it says that each test pullback is represented by a scheme and that its projection is surjective. I checked the other projection explicitly by evaluation of a natural transformation at the identity; naturality recovers all its components. The equation f_T p = f_U v follows because both projections are over S. This is an elementary unpacking, not a claim that an arbitrary sheaf surjection has a section. The citation quote includes the representing-scheme and surjectivity clauses verbatim.

Step 2 uses no theorem: for an arbitrary t choose z above it by the given scheme surjectivity, and write f_T(t) = j(u(v(z))). This is the entire image argument, with no hidden topological theorem and no point-lifting claim over a fixed residue field. It requires only the assumed factorization of U -> S.

Step 3 cites `lem-weil-pbc-morphism-factors-through-open-subscheme`; its statement explicitly says there is a unique morphism h' with j_U h' = h. Here h is f_T and its image containment is precisely step 2. Both objects are schemes and W is an open subscheme, so the hypotheses match. This is the one step marked non-elementary.

Step 4 reuses that exact uniqueness clause on T'. Both competing maps compose with j to the structural map f_T', by the over-S condition on r. This proves the required naturality by an elementary substitution. It uses neither the proof of the cited node nor an uncited monomorphism theorem.

Step 5 uses the representable-functor formula and the definition of algebraic-space morphisms as natural transformations in `def-trf-algebraic-space`, together with the same unique-lift statement. I checked the displayed formula a_y(V)(s) = Y(s)(y): its compatibility with restriction gives a_{Y(r)(y)} = a_y h_r. Thus step 4 is exactly the naturality equation for b. The componentwise composite with h_j is the structural map. For uniqueness an alternative component is a scheme map lifting that same structural map, so the cited uniqueness applies. Finally evaluation at id_T and naturality recover every arbitrary test a from a(T)(id_T); this verifies that the construction gives the test maps asserted by the item. No appeal to a Yoneda theorem with a narrower statement is hidden here.

For E I checked every hypothesis where used: representability and scheme-test surjectivity only in step 1, the assumed U -> W map in step 2, openness only in step 3, and the over-S identities in steps 1 and 4. The proof works for arbitrary W and non-affine U; it never uses etaleness. Small cases: W=S gives the structural maps themselves; W empty forces U empty and every test T with a section of Y to be empty by P -> T surjectivity; empty test schemes have their unique maps throughout. Empty Y introduces no nonempty test sections and no exception to the natural-transformation construction. Nilpotents do not interfere: image containment suffices for an OPEN subscheme by the cited theorem. For contrast an arbitrary closed immersion would not permit this inference, and I did not use such a claim. No new statements needed separate small-case testing.

For C/D the proof-dependency union is exactly the citations in the steps, each quotation comes from its node statement, no source proof is used as a substitute for its statement, and no new clause-sized node or circular citation was introduced. Every elementary step has its actual argument written out. All five steps are below 2000 characters. The expansion corrected the absence of proof and made naturality and uniqueness explicit; it changed no mathematical statement or source route. No second agent was used, as required by the direct-delivery brief.

## Unfinished work

None in the requested stage-1 split. Server dry run and direct delivery follow this report.
