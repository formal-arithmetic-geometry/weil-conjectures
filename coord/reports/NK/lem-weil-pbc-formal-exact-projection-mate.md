# NK: lem-weil-pbc-formal-exact-projection-mate

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-formal-exact-projection-mate.json`: statement, split; seven proof steps; Mathlib has the general composition and whiskering tools, but no matching declaration for the complete statement with only exact bifunctors and natural right actions.
- `citations.json`: one exact statement quotation for every step/node citation.
- `searches.jsonl`: actual results logged by msearch.py. The item's inherited searches are retained and the six searches made during this split are appended without altering their query text.
- `report.md`: this report. `write_split.py` is a sandbox-local preparation script, not a DAG delivery file.

No new nodes and no new Mathlib leaves. Statement and statement dependencies are unchanged. No unit record changes: this item is a formal auxiliary calculation below the unit's perfect-projection-formula route.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for projection/mate/shift/unit terminology. The closest project declarations are `CategoryTheory.Adjunction.commShift_rightAdjointProjectionMap_app` in `CategoryTheory/Adjunction/ProjectionMapShift.lean:184` and `CategoryTheory.Adjunction.rightAdjointProjectionMap_rightUnitality` in `CategoryTheory/Adjunction/ProjectionMapMonoidal.lean:96`. Read their hypotheses and proofs. The former supplies the shift clause; the latter is stated for monoidal categories. Neither, nor their conjunction, states every clause of the item with its weaker bifunctor/right-action hypotheses. I do not claim an attachment based on these partial matches.

## WANTED

None. All sources used were available locally.

## Audit of the starting node and route

The item arrived with an empty proof and a complete, explicitly specified-data statement; there was no earlier sandbox split or report. Its current statement is mathematically sound. No STATEMENT-DISPUTED correction is needed. The distinction between supplied data and construction of ringed-site derived data is maintained throughout. No invertibility of the mate is asserted or used.

Read the chapter and unit records and the current main-20261015 perfect-projection-formula blueprint text. The blueprint ancestor is `lemma-weil-pbc-perfect-projection-formula`; this auxiliary item serves the first-paragraph shift/cone closure and normalization at the coefficient unit through `lem-weil-pbc-ringed-projection-mate-exact`. The latter is an ancestor, not a dependency used to prove this item. The proof uses no coefficient-category comparison, no proper base change theorem, and no purity source.

Read Stacks `sites-cohomology.tex`, Tag 0B56, `equation-projection-formula-map` (lines 13666 onward): the map is the adjunct of the pullback tensor comparison followed by counit tensor identity. Read `derived.tex`, Tag 014V, `definition-exact-functor-triangulated-categories` (line 191 and the following definition of a compatible transformation), Tag 014Y, `lemma-composition-exact` (line 939), and Tag 0A8D, `lemma-adjoint-is-exact` (line 2290 and its unit/counit shift calculation). The item assumes exactness and adjunction compatibility, so none of the existence or Yoneda arguments in 0A8D is needed. The full seven-step formal calculation is written here and marked agent-origin; it is not attributed as a verbatim Stacks theorem.

Searched the whole DAG for Tag 014Y/composition of exact functors and projection/shift/unit statements and used the existing composite leaf. Ran `tools/blueprint_refs.py ancestor` for the item and `search` for projection mate, projection formula, and triangulated functor. The imported blueprint matches describe geometric or monoidal projection formulae, not this specified-data formal theorem. The existing first-input ringed projection shift node depends on the ringed-data ancestor and cannot be used here. No duplicate node was created.

Mathlib searches were run only through msearch.py: LeanFinder with two phrasings, Loogle, LeanSearch, and two source greps. Read the returned shift transformation and monoidal adjunction hits. The projection-specific grep and Loogle searches returned zero hits; the broader grep returned general category composition instances, not a projection theorem. Read Mathlib `CategoryTheory/Shift/CommShift.lean:343–433` (compatibility for every monoid element, composition and both whiskerings) and `CategoryTheory/Triangulated/Functor.lean:244` (the exact-composition instance), verifying the existing leaves used. The original searches already stored in the repository node were preserved rather than presented as searches of this worker.

## Not duplicates

No new nodes. Existing exact-composition, adjunction, triangle, and shift-calculus nodes are reused. In particular no extra node is introduced for the unit normalization or the connecting square: their calculations are in the item's proof.

## Review by NK

I checked sections B through E of delivery-errors.md, including the retired newtargets copy, against the actual statements and the local sources above. There are no new node statements to source or test. Every statement dependency defines the notion the item uses: triangulated/exact categories and functors, specified adjunction unit/counit formulas, composite shift comparisons and compatibility, and the three equations for a triangle morphism.

Step 1 uses the full statement of `lem-weil-pbc-triangulated-functor-composite`: it gives the particular composite comparison, and preservation of distinguished triangles with that connecting arrow. Applied successively to L, tensor-by-E, and R, its hypotheses are exactly the supplied exactness hypotheses. `def-weil-triangulated-category` states the exact-functor notion. F itself is the supplied second-input tensor functor. No assertion that an arbitrary adjoint is exact is smuggled into this step.

Step 2 uses the adjunct formula and naturality of unit/counit stated in `lem-weil-pbc-adjunction-of-natural-bijection`. I checked the equation for simultaneous maps e and p: the source is L(RE tensor P), the target is E' tensor LP', and the counit naturality is e epsilon_E = epsilon_E' LR(e). Applying R and naturality of eta proves simultaneous naturality of alpha. This is an elementary calculation from supplied naturality and the cited formulas, not a new lemma about derived functors.

Step 3 uses the composition and whiskering clauses of `lem-weil-pbc-commshift-nattrans-comp-whisker`, whose actual statement I read. Its arbitrary shift auto-equivalence can be taken to be each [n]; the underlying Mathlib leaf is explicitly indexed by every element of the shift monoid. The two squares being composed are given explicitly. One is the hypothesis for mu; the other is the naturality of the supplied tensor shift comparison in the fixed input, at epsilon_E. Without that latter hypothesis the argument would have a gap. It is present in the item. No naturality of epsilon in a shifted E is needed here because E is fixed.

Step 4 uses the same leaf's whiskering and composition clauses and writes out the resulting equality. I checked the intermediate unit equation by first using eta naturality at f_(n,P): F(P[n]) to (FP)[n], then the assumed shift compatibility of eta at FP. The naturality of r is applied to beta_P: A(P) to H(P), which is correctly typed. This proves every integer-shift square, without importing a statement that constructs shift structures for unrelated adjoints.

Step 5 cites the exact three equations in `def-weil-pbc-triangles-with-shift`. The first two follow from step 2; the last is displayed, using naturality at the actual arrow w: P3 to P1[1], then step 4. Both triangles are already distinguished by step 1. Thus this is an elementary substitution, with no unproved claim that connecting maps are compatible.

Step 6 uses only the supplied right-unit axiom, bifunctoriality, and naturality of the supplied right action at epsilon_E. I checked all three displayed expressions have source L(RE tensor 1_C) and target E. There is no associator, braiding, or additional monoidal axiom. Step 7 uses the natural unit and the triangle identity explicitly stated by `lem-weil-pbc-adjunction-of-natural-bijection` (also hypotheses of this item). Naturality at rho_RE moves RL(rho_RE) across eta; R(epsilon_E) eta_RE then equals identity. This gives the exact normalization equation, not merely an isomorphism at the unit. The verbatim quotes in citations.json were extracted from these actual node statements and checked as substrings.

I tested the types and limiting cases: n=0 yields the ordinary identity comparison and n<0 uses the given coherent inverse shifts; no positive-shift induction is assumed. E=0 gives zero source and target by additivity and causes no cancellation argument. Identity L=R with identity tensor comparison makes beta and alpha identities, and the formula reduces to rho_E=rho_E. With nonidentity u and right actions the proof retains k_E and uses the exact supplied compatibility, so does not silently identify L(1_C) with 1_D. Split or zero triangles satisfy the displayed third-square equation directly. The proof never cancels the counit or assumes alpha invertible.

I checked the dependency union and all quoted statements, and kept proof_origin as agent for the formal expansion. All seven steps are shorter than 2000 characters. Elementary steps are only naturality/bifunctoriality substitutions and the explicitly supplied triangle identity; the two closure lemmas are cited in non-elementary steps. No unproved comparison or statement clause has been moved into a new node. All writes are in the specified sandbox, no Lean or compiler commands were run, and no forbidden SGA source is used.

## Unfinished work

None in the stage-1 split. Maintainer review and later Lean implementation are separate stages.
