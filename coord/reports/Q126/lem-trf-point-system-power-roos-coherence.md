# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-point-system-power-roos-coherence.json`: statement, split into seven steps, not a Mathlib leaf. Statement unchanged; no new nodes and no new Mathlib leaves.
- `citations.json`: one literal statement quotation for each node used by each proof step.
- `report.md`: this report. The sandbox also retains `searches.jsonl` and the preparation script.

## Attachments

None. Searched the project Lean source for the exact blueprint tag and point transport, insertion, powers and Roos terminology. The tag and a declaration stating this entire assertion were absent. Read the relevant parts of `WeilConjectures/SixFunctors/Etale/Derived/AdicSystem.lean`: its normalized étale systems and geometric-stalk coefficient comparisons do not give the arbitrary strict pro-étale semilinear systems and normalized whole-cone compositor here. `WeilConjectures/Algebra/Homology/RoosComparisonMaps.lean` gives ordinary tower cone comparison maps, not the required point-system power law. Neither is an attachment.

## WANTED

None.

## Findings and repairs

The item was unsplit and the sandbox had no previous attempt. Its source-place annotation says “Step 1, Global powers,” but that sentence is actually in the current `thm-trf-l-function-euler-product.proof.md`, rather than the rational-integral-model proof file recorded in its source. Read both files: the latter's clauses (2)–(4) provide the reduction and iterated-transport context. The proof provenance and individual step sources now identify the actual global-powers sentence and its supporting Stacks material explicitly. The statement, original source annotation and blueprint ancestry are retained.

The split separates the finite insertion calculation from strict quotient-transition compatibility and localization. For the limit assertion it checks the exact-product hypotheses, writes the diagonal product comparisons, verifies their composition by product projections, verifies both cone coordinates with their differential, and finally cancels the specified normalized Roos identifications. Thus the conclusion concerns the specified maps, with no appeal to equality detection by derived evaluations. No completeness, cartesianness, Tor-amplitude, boundedness or constructibility hypothesis was added.

## Searches and reuse

Ran the required `msearch.py` commands as Q126: two distinct LeanFinder phrasings, Loogle, LeanSearch, and two Mathlib grep patterns. Every query and its actual result is in `searches.jsonl` and was added verbatim to `mathlib_searches`; pre-existing Q89 search records were retained. Read the returned types: ordinary inverse-system and LightProfinite projection statements, affine-scheme comparisons, binary product-comparison composition, and `CategoryTheory.Limits.piComparison` cover ingredients, not this whole assertion. The product-projection uniqueness argument is a few-line elementary proof, not a new node.

Searched the whole DAG and `blueprint_refs.py` for Roos, point transport and product comparison. Reused the existing finite `lem-trf-point-sheaf-insertion-calculus`, coefficient-composition, exact-product and normalized Roos nodes. No imported blueprint node states the combined assertion in another form, so `blueprint.same_as` remains empty. The item is not the key statement of its unit, so no unit realization record is changed.

## Not duplicates

No new nodes. The finite insertion-calculus node supplies a single-ring sheaf calculation; this item adds actual quotient-linear transitions and a whole derived-limit compositor. The existing exact-product-functor nodes supply the normalized comparison and its projection formulas; the item proves its composition formula explicitly instead of creating a second comparison lemma.

## Review by Q126

I read `GOAL.md`, the chapter and unit records, the three-level route in SETUP, and both copies of delivery-errors B–E. The chapter reference to SGA 5 is not used here: the argument uses the current blueprint and Stacks, with no SGA source. The source is the current Euler-product proof, Step 1 “Global powers,” specifically its asserted compatibility with composition. I also read the rational-integral-model proof's reduction/iteration paragraphs, Stacks sites.tex Tag 03CB (`lemma-composition-morphisms-sites`) and Tag 0H7J (`example-constant-sheaf`), and sites-cohomology.tex Tag 0941 (`lemma-derived-limit-is-ok`) and its proof. The additional normalized, exact-product coherence is an agent-written refinement, and `proof_origin.by` says so. There are no new-node sources to review.

For Step 1 I opened `lem-trf-constant-coefficient-composition`: its statement gives precisely the constant-ring compositor equation, with the canonical adjunction-compatible inverse-image isomorphism. `lem-weil-proetale-isomorphism-inverse-image` supplies compatibility with ring maps, including coefficient reductions. The completed coefficient projection equation is explicitly in `def-weil-inverse-image-pullback-comparison`; equality after all coefficient-limit projections is an ordinary limit universal-property argument. Here the scheme maps are isomorphisms and the finite coefficients are the specified finite quotients, so the hypotheses match. This verifies the transported completed-module actions before any product comparison is used.

For Step 2 I opened `lem-trf-point-sheaf-insertion-calculus`. It states both the normalization at the reindexed object and the exact point-insertion composition equation, for each finite commutative ring and an arbitrary module sheaf, then extends it to complexes. `lem-trf-point-system-transport-descent` specifies the very same restriction/insertion/sheafification/unit recipe. The pullback-composition node specifies the canonical termwise compositor, and part (a) of the inverse-image comparison defines the finite pullback here by the exact ordinary tensor pullback. This justifies using that compositor for arbitrary degrees, without assuming the complex is K-flat. All finite identifications are read through the prescribed j maps.

For Step 3 the descent node explicitly supplies differential and actual quotient-transition commutation as well as the localization and identification with I. I checked the transition formula with rho_n(1)=1 and the scalar compatibility from Step 1. Equality in a category of strict towers is componentwise equality of its natural transformations; this step localizes that existing equality. It does not infer equality of derived morphisms from evaluated equality. This step is elementary after the cited construction.

For Step 4 the product-exactness node explicitly applies to every ring sheaf on the small pro-étale site, hence to the completed coefficient sheaf. The isomorphism-inverse-image node gives exactness and preservation of all small limits, including countable products. The inverse-image comparison's scalar-transport paragraph identifies the relevant module functor. I checked these are precisely the hypotheses of `lem-cbc-exact-product-functor-strict-limit`. Its statement specifies the theta-inverse/kappa/F(theta) formula on both coordinates with no boundedness condition. The strict Roos comparison supplies the normalized natural total-limit identification; the chain-maps node supplies the projection formulas and naturality on strict complexes.

For Step 5 the chain-maps node supplies exactly the defining projections used, and the proof writes out the two equal composites with every product projection. This is product uniqueness at the strict complex level. For Step 6 the strict-limit node states the signed coordinates and differential; the strict Roos node states that strict commuting squares induce the cone functor and descend. The proof checks the shift using the actual transitions and then compares the two diagonal entries in every degree. I checked both off-diagonal entries vanish and the differential is compatible; no connecting-map compatibility is hidden here. These steps are elementary matrix/projection calculations from those stated constructions, not proposed new lemmas.

For Step 7 I checked the types in the theta-conjugation formula. Naturality of theta gives the displayed expression for the limit of T; naturality of d gives its expression on H(X). Expanding both sides cancels the two adjacent inverse-isomorphism pairs and leaves the same map. The strict Roos statement supplies natural descent, so the result holds for arbitrary C in the ordinary unbounded derived system category. This uses the statements of the two cited nodes, not their proofs. All step citations have literal statement quotes in citations.json.

Small cases checked: m=1 gives the twofold reindexing and multiplies exactly two tensor units; a zero system makes every map zero; systems with zero, identity or non-surjective transitions all satisfy the same shift equation because only naturality of the given transitions is used. For a complex supported in one degree the shifted coordinate still occurs in the adjacent cone degree, and the proof checks it too. Noncartesian and unbounded systems require no extra input: exact products and the normalized Roos statement have exactly that generality. A nonzero off-diagonal cone map could have the same ordinary evaluations, which is why this proof fixes and compares the diagonal representatives instead. No statement dispute arose.

No proof step exceeds 2,000 characters. Generic exactness, pullback composition, and normalized total-limit nodes are declared as tool uses in split_report where outside the unit; the unit's route through reduction and transport is preserved. The independent maintainer review remains the delivery's next mathematical review; no second worker was started.

## Unfinished work

None in the one-level split. Existing unsplit dependency nodes remain their own future items.
