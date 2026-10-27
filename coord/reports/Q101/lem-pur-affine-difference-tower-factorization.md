## Worker report

1. Files written: `dag/nodes/sec-smooth-purity/lem-pur-affine-difference-tower-factorization.json` (statement, split; Mathlib searches find component facts but no theorem for this entire coordinate tower) and `citations.json`. No new nodes or Mathlib leaves. The other sandbox files are local preparation/search records, not delivery files.
2. Attachments: none. Searched the project source both for the exact blueprint tag and for difference/affine/tower and coordinate normal-form terminology. The deformation-space coordinate declarations concern a different construction; none states this item.
3. WANTED: none.
4. The imported item had a statement but no proof. Its statement, including every hypothesis and conclusion, is preserved. No STATEMENT-DISPUTED issue was found. The blueprint's short reference to standard coordinates is expanded into actual morphisms and reversible test-scheme descriptions. I did not treat an arbitrary etale map as separated or quasi-compact: affineness is established first, and finiteness and separatedness are then obtained for these particular affine maps.
5. Nothing remains unfinished in the one-level split. Existing statements remain dependencies to be handled by their owners.

## Sources and searches

I read GOAL.md, the stage-1 brief and stage rules, the worker contract, the three-level route in SETUP.md, both copies of delivery-errors.md B-E, the smooth-purity chapter and unit records, and the current main-20261015 proof of thm-pur-composition-coherence. The latter's Step 1 is the route: standard etale coordinates and the canonical product identifications of the diagonal tower. This is a geometric subargument on that route, independent of coefficient or exceptional-functor choices. The proof is marked agent-written because the detailed coordinate calculations expand the blueprint's argument rather than reproduce a written literature proof.

For the geometric inputs I read Stacks morphisms.tex, labels lemma-composition-etale (02GN), lemma-base-change-etale (02GO), and lemma-smooth-etale-over-affine-space (054L), including the chart proof. I also read schemes.tex, lemma-fibre-product-affines and its tensor-product proof. The remaining geometric facts are used through their existing DAG statements, all of which were opened and checked. No new result is asserted on the strength of a definition of a morphism property.

Before considering new nodes I searched the whole DAG by chart, relative-dimension, etale-stability, affine-product, separatedness and finite-type concepts, as well as relevant Stacks tags. Blueprint searches for etale coordinates, affine space, difference, coordinate difference and Cartesian tower found no duplicate of the item. `blueprint_refs.py ancestor` confirms thm-pur-composition-coherence, with lem-pur-diagonal-section-pasting as the intermediate created item. All useful geometric components already have nodes, so none was created.

The five exact Mathlib queries already recorded on the imported node were rerun through the required msearch.py command for Q101 and their results read. LeanFinder returned standard-smooth polynomial-chart and standard-etale algebra facts. LeanSearch returned affine-map subtraction, smooth composition, etale cancellation, and relative affine-space maps. Loogle returned etale stability and definitions. The grep hits concern combinatorial diagonals rather than scheme coordinate differences. The second LeanFinder phrasing returned standard-etale presentations and etale composition, not the tower statement. The Mathlib source search used only msearch.py; no compiler or Lake command was run.

## Not duplicates

No new nodes. In particular the split reuses the existing etale base-change/composition, affine fibre-product, affine-source separatedness, affine etale finite-generation, smooth-dimension permanence, affine-space smoothness, and local-normal-form nodes.

## Review by Q101

I checked the node against B-E rather than accepting the blueprint's coordinate shorthand. There is no new statement needing an independent proof or search audit. For each proof step I read the statements named in `uses`; citations.json quotes them verbatim, including the relevant clauses. The independent maintainer can therefore check that the proof takes assertions from statements rather than from hidden constructions inside another proof.

Step 1 uses the polynomial affine-space definition and fibre-product universal property. Subtraction by a base function is an actual polynomial automorphism, with addition as inverse. The ordered polynomial variables give q as the base change of P_d; this does not assert an unproved invariance theorem. This step is elementary.

Step 2 uses the same definitions and the explicit affine-spectrum fibre-product theorem. Its statement gives both the tensor ring and its projections, so it really supplies affineness of Q, W, W_f and V times_T V. The first block of R is free and its second block is forced by G, proving R = A_Q^d and the formula for J without a separate comparison lemma.

Step 3 uses clause (1) of etale-base-change-finite-limits only for base change of the supplied g chart. The open-immersion definition and clauses (1)-(2) of etale-composition-cancellation justify composing with the explicit translation automorphism. The map used to base change g is gf:B -> T, not f:B -> V. No finiteness hypothesis on that base map is needed by the cited clause.

Step 4 proves W = Q times_V U directly, with Q -> V the second projection, and applies the same two etale-stability statements to the given f chart and the proved G. This checks the actual bases of H and J. It proves etaleness of F by composition, not by presuming that the composite-coordinate map is etale.

Step 5 evaluates the actual coordinate formulas. I checked the order (x block before y block), the signs, and the identities on the base ring and all polynomial generators. The zero-section equations therefore hold for morphisms of schemes, including nilpotent test functions. This step is elementary.

Step 6 uses affine-source-morphism-separated, whose statement permits the affine sources just proved, and etale-ring-map-quasi-finite, whose statement explicitly supplies finite algebra generation for an etale map of affine spectra. Only that finite-generation clause is used. Finite type for these affine maps follows by the finite-type affine criterion; there is no illicit general assertion that etale implies globally finite type.

Step 7 uses affine-space-smooth for all four actual affine projections and the base-change clause of smooth-relative-dimension-permanence for q. The latter explicitly preserves the specified dimension under arbitrary base change. The composite P_e q is P_(d+e) by the coordinate projection, so there is no hidden additivity argument for that assertion.

Step 8 checks the square involving H_f on arbitrary test schemes. Equality of the Q components imposes fu'=fu; equality of the remaining coordinates uniquely determines the first block. This proves W times_R A_B^d = W_f scheme-theoretically. The only non-elementary consequence is etaleness under base change, which its cited node states.

Step 9 checks the other square on arbitrary test schemes: the first coordinate v is forced to be fu, and v' remains free over T. The coordinate difference is then exactly y(v')-y(fu). I separately proved etaleness of G_g using the base change of the supplied chart along g followed by its translation; etaleness of G alone would not establish that conclusion. The diagonal identities are literal subtraction identities.

Step 10 applies normal-form existence successively, first to g at f(x), then to f with target restricted to the resulting V_1. The latter may shrink V_1, but the previous g chart restricts by an open immersion and stays etale by the cited composition statement. The cited affine-space smoothness and smooth-dimension composition give the dimensions r and s of the two restricted maps. At f(x) and x these equal the supplied pure relative dimensions e and d, so the chart sizes are the required ones. The lft-affine-pairs statement explicitly applies to every affine open, hence proves finite generation over k for U, V and T without assuming their ambient schemes affine. These algebra generators also prove finiteness of the restricted maps; separatedness uses their affine sources. No absolute separatedness of X,Y,Z is added.

Step 11 checks zero-sized polynomial blocks and empty affine spectra. With d=0 or e=0, the corresponding translation and polynomial block are the identity and A^0_B=B. With B empty all coordinates live in the zero ring; with U empty but other charts nonempty the same supplied base-change diagrams still work. With V or T empty the maps force the appropriate sources empty. No step chooses a point of an empty scheme; the localization clause begins with a supplied x and is vacuous for empty X. All these checks agree with the empty-scheme clause of smooth-dimension permanence. There are no divisions, reducedness assumptions or dimension comparisons of local rings in this argument.

I checked C1 and C4 for every non-elementary step, and no step exceeds 2000 characters or packages an omitted lemma. The explicit coordinate and Cartesian calculations are steps, not new nodes restating clauses of the item. The geometric nodes from other units are declared in split_report.tool_uses as generic tools; they do not replace the purity unit's diagonal/standard-coordinate route. No SGA source is used.
