## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-bounded-below-square-localization.json`: split into four proof steps; statement unchanged; no new nodes.
- `citations.json`: six verbatim citation entries, checked against the actual statements.
- `report.md`: this report and Q40 review.

Attachments: none. The item id has no declaration under `lean/WeilConjectures/`. Concept searches there found PlusAdjunction.lean's `derivedPlus_mateEquiv_app_fac`, which assumes the localized square and its factorization as hθ; it does not construct or uniquely characterize it. `CategoryTheory.boundedBelowDerivedSquare` in `lean/Sheaf/CategoryTheory/BoundedBelowDerivedMateModel.lean:53` constructs it, but is outside WeilConjectures and is not an attachment under the brief. Its factorization/uniqueness are expanded in the delivered proof.

WANTED: none.

The imported item had a statement but no proof. There is no statement dispute. No source, chapter, unit or route change was needed. In particular the item has neither an invertibility hypothesis on σ nor an enough-injectives hypothesis, and neither has been inserted. The proof first works on bounded-below cochains; the existing cochain-localization lemma avoids confusing strict boundedness of terms with boundedness of cohomology. It then returns to the homotopy notation in the item's statement.

Nothing remains unfinished in this one-level split. All non-elementary inputs are existing Mathlib leaves: exact-functor factorization, bounded-below cochain localization, and the localization universal property on natural transformations.

## New nodes

None (0 new nodes, 0 new Mathlib leaves). The three existing Mathlib leaves were read in full and reused. In particular no separate node is needed for composing the two comparison isomorphisms or for the termwise naturality calculation.

## Searches and blueprint

Searched the full DAG by `fullyFaithfulWhiskeringLeft`, localization/natural-transformation and precomposition/fully-faithful concepts; opened the resulting `lem-weil-pbc-localization-universal-property`, `lem-weil-pbc-bounded-below-cochain-localization`, `lem-weil-pbc-exact-functor-derived-factorization` and the definitions of D and D-plus. The localization-universal-property node includes existence AND the conjugation formula AND uniqueness, rather than just a definition or full faithfulness claim.

Ran `tools/blueprint_refs.py search` for `localization`, `exact functor`, `natural transformation`, `bounded below square` and `localization universal`, and `ancestor lem-trf-bounded-below-square-localization`. None of the imported blueprint nodes states this exact composite-square result. The ancestor is `lem-trf-local-term-locality`. Read the current latest proof of that node, including the normal-cone specialization route, and the trace-formula chapter and sk-i-curve-zero unit records. The existing long ancestry records precisely the ph/etale comparison branch of this route. The split retains its from.place and via and records the relationship in split_report.blueprint.

Ran the required msearch command for this item with LeanFinder, Loogle, grep, LeanSearch, and a second LeanFinder phrasing. Read every result, then the pinned Mathlib implementations. The successful Loogle query returns liftNatTrans and liftNatTrans_app, while LeanFinder returns exact-functor comparisons or derivability/Guitart lemmas. These are ingredients already represented in the DAG: forming the two composite functors and comparisons and relating cochains/homotopy objects still requires the delivered assembly, so the entire item is not recorded as a one-line Mathlib specialization. All new search records use the exact query and result from searches.jsonl. The old inherited search records are retained as historical data, including their unavailable and invalid-query verdicts; no claim is made to have rerun them.

## Not duplicates

No new-node/existing-node pairs: this delivery creates no nodes. The general localization result already exists and is cited rather than duplicated.

## Review by Q40

I read the construction `boundedBelowDerivedSquare` in `lean/Sheaf/CategoryTheory/BoundedBelowDerivedMateModel.lean:45–73`, and the hypothesis hθ of `derivedPlus_mateEquiv_app_fac` in the current upstream PlusAdjunction.lean:419–429. They have the same comparison direction as the item: from E'T(qN) first to E'(qK(G)N), then to qK(L')K(G)N; the other comparison starts at SE(qN). The source construction inverts the two comparison isomorphisms where appropriate and never inverts σ. This is exactly the formula in the item. The four abelian categories, all four exact additive functors and common size convention are retained.

I also read Stacks derived.tex, lemma-additive-exact-homotopy-category (014X), lemma-right-derived-exact-functor (015F), and lemma-bounded-derived (05RW), including the latter's bounded-representative proof. The exact-functor lemma permits every complex to compute the derived functor without resolutions. The bounded-localization result is for arbitrary abelian categories, not just those with enough injectives. For descent of natural transformations I read Mathlib/CategoryTheory/Localization/Predicate.lean:278–336. Stacks 04VG in categories.tex is only the functor-factorization statement; I do not misattribute the natural-transformation clause to it. That clause is explicitly present in the cited DAG statement and in Mathlib's liftNatTrans, liftNatTrans_app and natTrans_ext. I marked the expanded assembly as agent-written rather than claiming Stacks contains the full square proof.

Step 1 uses `lem-weil-pbc-exact-functor-derived-factorization` for preservation of quasi-isomorphisms and the given localization comparisons. Its statement says both. The other assertions in this step are direct calculations: an additive functor maps zero terms and homotopy equations to zero terms and homotopy equations; naturality of σ for the differential gives a chain map, and naturality for f^r gives naturality on complexes. No theorem about exactness of a natural transformation or injective preservation is being used.

Step 2 again uses the actual natural comparison of that same node. I checked all intermediate objects in A_N and B_N; their isomorphisms are natural by whiskering and composition. This step is elementary relative to those given comparisons and the definition of a bounded-below cochain complex. There is no additional composition-coherence theorem being silently used: the explicit composites A_N and B_N are precisely the comparisons supplied to the lifting problem, without replacing them by another independently chosen composite-functor comparison.

Step 3 uses `lem-weil-pbc-bounded-below-cochain-localization`, whose statement explicitly supplies localization of CoCh-plus at quasi-isomorphisms and the comparison with the ambient cochain localization. It uses `lem-weil-pbc-localization-universal-property` clause (2), whose statement explicitly gives the unique lifted natural transformation with the formula φ₂⁻¹ τ φ₁. I substituted F₁=Q⁺C(L')C(G), F₂=Q⁺C(H)C(L), and their specified lifts E'T, SE. All functors have the same source CoCh-plus(B) and target D-plus(A'); both invert the same quasi-isomorphisms. The output formula becomes exactly B_N⁻¹ q(σ_N^K) A_N. Passing from cochains to their homotopy classes uses the quotient described in the cochain-localization node, not an assumption about a small index category or a resolution.

Step 4 uses clause (3) of the same universal-property statement on the localization supplied by the cochain-localization node. Cancellation is legitimate because only B_N is cancelled, and it is an isomorphism. The cochain representative components determine a natural transformation on the whole D-plus, including objects whose terms themselves are not bounded below in a chosen unbounded representative. This verifies the uniqueness quantifier rather than merely proving a formula on one chosen complex.

I tested σ=0, σ an identity, all categories the zero abelian category, and zero complexes with arbitrary lower bounds. Zero σ gives the conjugated zero map and requires no inverse; identity squares give precisely the identification determined by A and B (they need not be literally identities under non-strict comparison choices). Nothing depends on choosing a nonzero object, a uniform lower bound for all complexes, or enough injectives. There are no new statements requiring separate small-case tests.

Against delivery-errors B–E: there are no new unsplit statements, proof sketches hidden in statements, duplicate nodes or Mathlib facts turned into new work. The statement and all existing metadata are retained. Each cited statement was opened, and citations.json quotes the exact part actually used; no step cites a definition for an absent theorem or borrows a node's proof instead of its statement. There is no forward or circular dependency on the derived-mate-model parent. All substantive localization facts are nodes, while termwise equations and composing comparison isomorphisms are written out. All four steps are shorter than 2000 characters; none hides a separate comparison lemma. I corrected the prospective citation for Step 2 to quote the actual natural-isomorphism clause, rather than just preservation of quasi-isomorphisms. I also chose cochain localization, whose complete interface is already in the DAG, instead of making an unsupported citation for a homotopy-only localization theorem.

## Validation

The required server dry run is run after this report is written. No Lean was written, no compiler or Lake command was run, and no repository or launcher file was changed.
