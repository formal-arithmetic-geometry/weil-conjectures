# Worker report: lem-coef-bipartite-cocartesian-simplex-extension

## Files written

- `dag/nodes/sec-six-functors/lem-coef-bipartite-cocartesian-simplex-extension.json`: statement, split into ten steps, unchanged statement and statement dependencies. Mathlib verdict: no exact match or one-line specialization. Zero new nodes and zero new Mathlib leaves.
- `citations.json`: 21 exact statement excerpts, one for every step/node citation.
- `report.md`: this report. `searches.jsonl` retains the five actual Q84 search results. The two sandbox Python scripts only prepare these files; they are not project changes.

## Attachments

None. Searched the whole `WeilConjectures/` tree of slopmaster2 for the exact blueprint id, bipartite, cocartesian simplex and last-vertex restriction terms. No matching project declaration exists. Read-only upstream master search also produced no matching project theorem; upstream is reference material only.

## WANTED

WANTED: Lurie, Higher Topos Theory, Propositions 2.1.2.5 and 2.4.1.7, Corollary 2.4.1.6, Remark 2.4.1.9 and the outer-horn discussion in Proposition 2.4.1.8, for this item. Read the online Harvard PDF, PDF pages 79-80 and 134-136 (printed pages 62-63 and 117-119).

WANTED: Lurie, Higher Algebra, proof of Theorem 3.1.2.3, printed pages 336 and 340-341, for the generic source-simplex/initial-inert-extension context. Read online; no download or literature modification performed.

WANTED: archival Kerodon Propositions 4.3.6.4 (018J) and 4.3.6.8 (01BZ), for the pushout-join and relative coslice lifting used here. These identifiers are Kerodon tags, not Stacks tags. No Stacks tag states this assertion about inner fibrations of quasicategories.

## Faults or changes to the inherited material

No statement dispute or source error was found. The inherited source points to the ambient operadic argument, while the item is a generic simplicial prerequisite. I made that argument explicit rather than assuming that the operadic source directly proves this more general incidence assertion. In particular, the bipartite section does not require operadic Segal decompositions, an ambient cocartesian fibration, or arbitrary cocartesian transports. Only the specified lifts are used.

The statement, its source record, ancestry, creation metadata and inherited searches were retained. `proof_origin.by` is `agent`: the proof is an explicit specialization and assembly of the cited generic lemmas, checked against online sources which are not archived in literature. The blueprint ancestor was confirmed by `tools/blueprint_refs.py ancestor`; its proof paragraph 2 is the coefficient mapping-complex adjunction, and the inherited operadic rectification branch supplies its coherent realization. The unit is the general biduality unit, not its key node, so no unit realization record is changed.

## Existing nodes and Mathlib searches

I searched the full DAG statement texts for relative slices, trivial Kan restriction, cocartesian initiality/composition, right-anodyne joins, and equivalence consequences. Whole-blueprint searches for `cocartesian`, `simplex extension` and `initial lift` returned no imported blueprint theorem identifying this item. The sibling `lem-coef-join-pullback-simplex-extension` was read but is not cited: its broader pullback construction is unnecessary. Existing nodes supply every non-elementary ingredient, so no new duplicate, elementary node, or rephrased clause of the item was created.

The Q84 search log records LeanFinder with both the cocartesian-incidence and final-vertex-relative-coslice phrasings, Loogle with `"SSet", "cocartesian"`, grep `cocartesian|coCartesian|relativeCoslice` under AlgebraicTopology, and LeanSearch with the full restriction/section statement. I read the returned signatures. I also opened Mathlib's ordinary `FiberedCategory/Cocartesian.lean:82-112`, `Quasicategory/Basic.lean:36-55`, `SimplicialSet/CategoryWithFibrations.lean:38-55`, `SimplicialSet/Coskeletal.lean:55-80`, and `ModelCategory/CategoryWithCofibrations.lean:96-112`. The ordinary cocartesian maps have strict categorical universal properties; strict Segal coskeleta reconstruct simplices of ordinary nerves; I/J are primitive boundary/horn generators; generic trivial fibrations only name a model-category class. None proves the relative quasicategory join restriction, initiality, and prescribed section theorem. The inherited earlier NC search entries remain intact and are not represented as Q84 searches.

## Not duplicates

No new nodes; there are no new/existing pairs to distinguish.

## Review by Q84

I read the complete item statement against the unit, the ancestor's coefficient-adjunction paragraph, HA's fixed-simplex extension discussion (printed pp. 336, 340-341), HTT's relative coslice restriction and cocartesian-edge results, and the Kerodon pushout-join and relative coslice propositions. The hypotheses retained are: small ordinary categories C and J, no composable nonidentity arrows in J, an inner fibration of quasicategories p, an arbitrary d-simplex tau, the specified whole-join base diagram g, and only the individual cocartesian cross-edge lifts s_a. In particular tau need not be nondegenerate and p need not admit other cocartesian lifts. The proof stays below the existing coefficient coherence branch; it uses no SGA reference.

For step 1, I opened the statement of `lem-cbc-relative-coslice-left-fibration`. Its actual map with K_0 empty and K a point is E_{x/} -> E times_B B_{p(x)/}; this is exactly what the proof pulls back to L^0 -> U. It does not claim that rho^0 -> N(J) itself is a left fibration. The base U is a pullback of the assumed inner fibration, so it is a quasicategory, as are its vertex fibers. I wrote the horn lifting and pullback identification explicitly. The definitions of inner/left fibration and nerve cited by this step supply the remaining vocabulary. This generic coslice theorem lies in another unit, so its tool use is declared in `split_report.tool_uses`; it changes no unit route.

For step 2, I read `lem-coef-infinity-cone-mono-right-anodyne`: it asserts right anodyneness for the cone of every monomorphism, including the empty-source map. For d > 0 its source cone is precisely the final vertex and its target cone is Delta^d; d = 0 is the identity. This avoids an uncited final-vertex theorem or a hidden horn filtration.

For step 3, I read the exact pushout-join clause of `lem-coef-infinity-anodyne-cocones`, and HTT Proposition 2.1.2.5's proof independently confirms the boundary-lifting conversion. The node takes a right anodyne first map and any monomorphism as second map, exactly j and the boundary inclusion. The proof uses the inner-anodyne clause, not the separate coherent-cocone mapping-space clause of that node. I wrote why an inner fibration lifts the weakly saturated inner-horn class. At k = 0 the domain still contains all of tau because join with the empty simplicial set is the original simplicial set; this is essential for vertex surjectivity.

For steps 4 and 5, I read `def-weil-pbc-trivial-kan-fibration`, `lem-weil-pbc-trivial-kan-lifts-monomorphisms`, and `lem-coef-joyal-model-structure`. Fiber restriction is proved by lifting the same boundary square with its base coordinate constant at a. Inner horns are monomorphisms, so the extension sources are quasicategories. The Joyal node explicitly states the weak factorization system (monomorphisms, trivial fibrations), so RLP against all monomorphisms proves categorical equivalence. No assertion that a Kan weak equivalence alone is categorical was used.

For step 6, I read `lem-coef-infinity-cocartesian-composition-initiality`, including its explicit simplicial coslice fiber L(x,f). Its initiality clause applies with source x, base arrow f_a and the specified lift s_a. The strict identification of J_a^0 with that fiber is given degreewise, using the constant simplices at a, not by taking a possibly non-fibrant homotopy fiber. Boundary dimension zero gives existence of z_a.

For step 7, I verified the whole initial-face convention in `def-cbc-enhanced-diagrams-cones`. The displayed monomorphism includes the entire initial Delta^k, not just its vertices, and includes the final point even for k = 0. Thus the general monomorphism lifting theorem applies with the actual prescribed pinched source and target. I opened `lem-coef-kan-quillen-right-proper`; its boundary characterization makes this map a weak homotopy equivalence, and the model-structure two-out-of-three property gives contractibility. This is a direct instance of an already cited lifting property with the displayed subcomplex, rather than a new comparison theorem or an inline unproved identification. It proves initiality for every vertex above s_a, not just for a convenient choice. No fully-faithfulness consequence absent from the categorical-equivalence node was assumed.

For step 8, I checked the horn orientation from `def-coef-infinity-fibrations`: Lambda^2_0 contains the edges x -> y_a and x -> y_b, and its missing edge is y_a -> y_b. The distinguished edge is s_a. I read the cancellation clause of `lem-coef-infinity-cocartesian-composition-initiality`; since s_a and s_b are cocartesian, the third edge is so too. The same statement includes degenerate edges, which handles all identity arrows.

For step 9, the only elementary assertion is the explicit gluing: a nondegenerate nerve simplex would require a composable string of nonidentity arrows, so none has dimension above one. Endpoints of every selected triangle agree exactly with the chosen s_a, and all remaining simplices are degeneracies. Hence the maps glue with no unfilled composition constraints. Parallel arrows are allowed and filled independently. This step only uses the nerve definition and the cocartesian conclusions already proved in step 8.

For step 10, I checked the monomorphism of the discrete vertex subset into N(J), including its degeneracies. The monomorphism lifting statement gives an actual lift with the specified z_a on that whole subset. Since R retains the N(J) coordinate and terminal block, both the section equation and the equality of terminal evaluations are strict. Every full tau is retained by the defining equations of L. Existence of some family follows from the vertex surjectivity already proved, in the project's usual choice convention.

Small cases: d = 0 makes R the identity; J empty makes both L and L^0 empty and all indexed claims vacuous; a discrete nonempty J has only independently chosen vertices; one nonidentity arrow gives exactly the single Lambda^2_0 lifting problem. Multiple parallel arrows create no additional simplex constraints. Degenerate tau and degenerate images of base arrows cause no failure: all lifting problems are over the specified simplicial map, with no nondegeneracy assumption. None of the ten non-elementary or elementary steps exceeds 2000 characters. There are no new statements to test and no hidden general-purpose lemma moved into a long step.

I checked delivery-errors B through E: no new-node issues arise; every cited statement was opened and exact excerpts recorded; all non-elementary facts are cited; the proof constructs the lifts and section rather than relabelling clauses; no dependency points back to this item; every application uses the hypotheses actually present. The changes from the imported item are its missing proof, explicit proof dependency union, current search records, and split report. No weakening, new hypothesis, hollow definition, Lean edit, compiler invocation or live project modification was needed.

## Unfinished work

No mathematical clause remains unfinished. Required dry run and push are performed after this report is written; their results are recorded below.

## Validation

The server `review_split` check returned PASS with zero new nodes. The required delivery dry run exited 0 and printed `OK (not pushed) deliver/Q84/lem-coef-bipartite-cocartesian-simplex-extension at 672dec57c0: preflight passed`. The report was then updated with this result, and the final report-inclusive dry run is rerun before direct push.
