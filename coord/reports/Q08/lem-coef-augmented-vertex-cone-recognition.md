# Stage-1 report: lem-coef-augmented-vertex-cone-recognition

## Files written

- `dag/nodes/sec-six-functors/lem-coef-augmented-vertex-cone-recognition.json`: item split; no new nodes.
- `citations.json`: three verbatim step citations.

## Attachments

- No new Lean declaration attachments.

## WANTED

- WANTED: archival copy of Lurie, *Higher Topos Theory*, Proposition 6.1.2.11 and proof (pp. 541–543), for the item. The source was read online as cited in the node.

## Review by Q08

I read the imported item, the `sec-six-functors` chapter and `sk-prop-sf-biduality-general` unit, and checked the corresponding source passage in HTT. I read the full statement of `lem-coef-infinity-terminal-pullback-criterion`, the only cited node. Step 1 is definitional: the maps from `[-1]` and `[0]` into `[n]` form exactly the stated star, so the pointwise cone condition is the first equivalence. Step 2 checks the base case `V_0` and writes the induction as a pullback of the previous apex with one copy of `A` over `B`, using the cited mapping-space pullback criterion. Step 3 checks the cartesian-square hypothesis supplies precisely that inductive pullback comparison and that its legs are the specified simplicial restrictions, so all cones are limiting. Step 4 checks the projection equations for a monotone `theta`, and uses pullback uniqueness and the simplicial identities to retain all coherences. I tested the edge cases `n=0`, `n=1`, and an empty augmentation source; no hypothesis was added or dropped. The imported statement and dependencies were otherwise unchanged.

## What was wrong or corrected

The item had an empty proof and unsplit status. I supplied the four proof steps and the exact proof dependency; no statement correction was needed and no duplicate child node was created. A candidate generic right Kan theorem was rejected because its dependency closure cycles back through this item, so the first clause is handled directly from the item’s pointwise definition.

## What remains

Nothing remains for this stage beyond the required dry run.


## Second reading by Q08

I independently read the sandbox item and current repository item, the full statements of all four final proof dependencies, `def-cbc-enhanced-diagrams-cones`, the chapter/unit records, the blueprint ancestor's derived-coefficient-adjunction proof paragraph, and HTT Proposition 6.1.2.11 with proof (printed pp.541–543; PDF pages 558–560) and Proposition 4.4.2.2/Remark 4.4.2.3 (printed p.296; PDF page 313), online. This is the ordinary Q08 stage-1 packet: the sandbox contains the item JSON and the exceptional Q20 recovery condition does not apply. No Lean was written or compiled, and the repositories and launcher were read only.

- Statement: PASS, unchanged byte for byte against the repository item. HTT's vertex slices give the same opposite comma star and Cech right Kan condition. The added finite-pullback formulation is the edge-gluing consequence, not a verbatim assertion of Proposition 6.1.2.11. Neither finite-limit completeness, terminal objects, groupoid hypotheses, realizations, nor effective epimorphisms are needed for this formulation.
- Step 1: FIX/PASS against the explicitly defined pointwise condition and the actual arrows of `(j downarrow [n])`: the comma arrows point from the empty-set object to vertices; its opposite is the star. Added the missing degree -1 check, where the identity cone on B is limiting. The enumeration is elementary; the identity cone comparison is explicitly the identity equivalence by the cited general cone criterion.
- Step 2: FIX/PASS against the full statements of `lem-coef-infinity-colimit-gluing` and `lem-coef-infinity-final-index-colimit`, and HTT 4.4.2.2/4.4.2.3. Applied oppositely; proved the indexing pushout and its monomorphism explicitly. The restricted limits are the old apex, B and A, so the required specific pullback is exactly the next iterated pullback. The old pullback-only citation did not state this gluing theorem.
- Step 3: FIX/PASS against `lem-coef-infinity-terminal-pullback-criterion` (including the square's specified coherence) and the gluing statement. Starts with the specified U_0 cone and uses each assumed U_(n+1) square as the particular pullback needed for gluing. No global pullback-existence hypothesis is imported into this clause. The full restricted U-cones and their overlap come from the same simplicial diagram.
- Step 4: FIX/PASS against `lem-cbc-enhanced-functor-cone-calculus`: its arbitrary-shape fixed-apex equivalence gives a contractible homotopy fiber over the complete restricted cone, and its terminal-object clause gives contractible limiting-cone identifications. The vertex equation is checked for every monotone map, including repeated coordinates. The explicit functor [k] x [2] to the augmented simplex category, using propagated vertices, supplies a prism of U with all augmentation/vertex compatibilities; the proof no longer infers them merely from vertex projection equalities. Marked non-elementary and cited the actual general cone theorem.
- New nodes: none; B1–B9 and child searches therefore have no new-node instances to check. No existing node was split again or modified besides this item. All new citations reuse current nodes; their dependency closures were opened and checked not to return to this item. The cone-calculus citation is declared as a generic tool use from another unit; gluing and final-index are in the item's unit.

Small cases: degree -1 is the identity cone on B, degree 0 the arrow A to B with limit A, and degree 1 the homotopy pullback of A over B with itself. For the nerve of sets, A empty gives empty limits in all degrees at least zero, and A=B with identity augmentation gives constant pullback terms. In spaces, A a point and B the circle gives a loop-space pullback in degree 1: homotopies in the square cannot be dropped, and identical leaf projections alone do not determine the coordinate map. The repaired argument uses the complete cone. An empty quasicategory has no augmented U, so the assertions are vacuous; the hypothesis on specified squares alone requires no terminal object.

Independent reuse/search check: searched the full DAG for star/Cech/gluing statements and both source checkouts for the item id and augmented-Cech/vertex-star vocabulary. No exact source attachment was found. Ran msearch.py with a fresh semantic phrasing, "The limit of a finite diagram of arrows to one central object is a repeated homotopy pullback in a quasicategory" (8 actual hits), and grep "widePullback.*pullback|pullback.*widePullback|[Cc]ech.*[Kk]an" in CategoryTheory (21 actual hits), recorded in searches.jsonl. Read Mathlib/AlgebraicTopology/CechNerve.lean:43–94: Arrow.cechNerve_obj/map and augmentedCechNerve use an ordinary Category C and ordinary wide pullbacks, so they do not state this quasicategorical criterion. None is a Mathlib leaf for the item.

Changes: corrected the opposite-comma wording and degree -1 coverage; supplied the existing gluing and initial-vertex limit results instead of taking their content from a cospan-only criterion; retained the precise specified square/cone in the induction; replaced the projection-only uniqueness claim with the full cone-space fiber and wrote the higher simplex restriction argument; made proof_origin agent because this expands the online, unarchived source; regenerated citations.json with full verbatim statements. Preserved the worker's original sections and .bak copies. No statement change, new node, Mathlib leaf, chapter/unit change, or forbidden SGA citation was introduced. The archival HTT request remains WANTED.

Preflight form repair: replaced the contextual phrase "the item's" in step 1 by "the stated pointwise convention for right Kan extension", retaining the complete objects and hypotheses already introduced in the statement. This was the sole reported preflight finding.
