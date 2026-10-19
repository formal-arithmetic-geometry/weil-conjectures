# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-segal-finite-cover-descent.json`: audited and split the imported item in six proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every cited node used by each proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and the upstream reference source for the item id, its blueprint tag, and the Segal finite-cover terminology. No sorry-free project declaration states this item exactly. The Mathlib declarations found by the recorded searches concern strict Segal simplicial sets and do not state descent for Reedy fibrant simplicial spaces with weakly equivalent Segal maps.

## WANTED:

WANTED: Rezk, *A model for the homotopy theory of homotopy theory*, archival local copy of Lemmas 10.1 and 11.11 (printed pp. 23 and 27), for `lem-coef-segal-finite-cover-descent`.

## What was checked and changed

I read the item node, the fixed `sec-six-functors` chapter and the `sk-prop-sf-biduality-general` unit. I searched the whole DAG and blueprint for the item statement, Rezk Lemmas 10.1/11.11, finite interval covers, and Segal mapping-space descent. The existing node `lem-coef-segal-equivalence-outer-horn` uses this item but does not duplicate it; it needs the finite-cover result for its outer-horn face family. No new auxiliary node was needed: the finite gluing induction is written as proof steps, while the model-category and mapping-space facts are supplied by existing nodes.

The imported statement was retained verbatim, including the empty-family case, singleton subsets, intersection-closed family, discreteness in the inner direction, and the requirement that every consecutive edge lies in each interval cover. The proof was expanded rather than replacing the claim by a clause or restatement. The item is marked `split`, with agent-written proof origin following Rezk Lemmas 10.1 and 11.11.

## Not duplicates

No new nodes were created. `lem-coef-segal-equivalence-outer-horn` vs `lem-coef-segal-finite-cover-descent`: the former is an equivalence-edge outer-horn restriction and cites the latter; this item is the general finite intersection-closed face-family gluing theorem. `lem-coef-segal-finite-cover-descent` vs Mathlib `SSet.StrictSegal.spineEquiv`: the Mathlib result is a bijective spine map for a strict simplicial set, whereas this item concerns weak equivalences of mapping Kan complexes for Reedy fibrant simplicial spaces and finite face covers.

## Review by NZ

I opened the statements of `lem-coef-simplicial-space-reedy-cartesian`, `lem-coef-kan-quillen-right-proper`, and `lem-coef-reedy-model-structure`, and checked every quote copied into `citations.json` against those files. Step 1 uses the Reedy cartesian mapping-space fibration clause to make every restriction map a Kan fibration and uses the definition of the mapping space to identify maps out of a union with a pullback over the intersection. The equality `F(S) ∩ F(T) = F(S ∩ T)` follows directly from the definition of the full face and is written out there.

Steps 2–4 prove the finite gluing assertion by strong induction on the finite intersection-closed family. I checked the maximal-member argument, the proper overlap family `T ∩ S`, its closure under nonempty intersections, and the two successive pullback decompositions. The only non-elementary inputs are the mapping-space pullback identity from step 1, the boundary lifting characterization of trivial Kan fibrations from `lem-coef-kan-quillen-right-proper`, and two-out-of-three from `lem-coef-reedy-model-structure`; the latter two are quoted in `citations.json`. Empty families and empty/disconnected overlaps are covered by the induction base and the same pullback argument.

Step 5 identifies the mapping space of the spine with the Segal map by evaluation at the top simplex. I checked the cases of zero and one edge separately, where the map is an identity, and the case `m ≥ 2`, where the item's weak-equivalence hypothesis applies. For an interval cover, the chosen interval faces cover the subobject, are closed under nonempty intersections, and their intersections with the spine are the corresponding spines; the finite gluing assertion then gives the interval-cover restriction. Two-out-of-three and the Kan-fibration property give the required trivial Kan fibration. Step 6 applies the same gluing assertion to the original family and checks the empty-family and singleton-vertex edge cases explicitly.

The Mathlib searches were run with `msearch.py` and are recorded exactly in the node and `searches.jsonl`: LeanFinder, Loogle, LeanSearch, and source grep, with alternate phrasings. Their strict-Segal hits were read in `Mathlib/AlgebraicTopology/SimplicialSet/StrictSegal.lean` and related files and rejected as non-matches because they do not state the Reedy mapping-space theorem. No Lean file was written, and no compiler, Lake, or build tool was run. The required server checks `check_dag` and `review_split` both passed.


## Second reading by NZ

- Item statement: checked each hypothesis and clause against Rezk §§2.3–2.5, §4.1 (4.1), and Lemma 10.1; the finite intersection-closed F(S) formulation and trivial-Kan-fibration conclusion are the stated split expansion. Empty family, n=0 and n=1, singleton S, and singleton/empty overlaps were tested and are covered.
- Step 1: checked the Reedy cofibration/fibration application against `lem-coef-simplicial-space-reedy-cartesian`; the union/intersection pullback identity is degreewise and the source description now records it as an explicit calculation.
- Step 2: checked the strong induction, maximal-member choice, closure of the reduced and overlap families, and all cardinality inequalities; no interval-cover hypothesis is silently used.
- Step 3: checked the pullback square, boundary-lifting argument for pullbacks of trivial Kan fibrations, and two-out-of-three against `lem-coef-kan-quillen-right-proper` and `lem-coef-reedy-model-structure`; disconnected and empty overlaps are included.
- Step 4: checked the identities for Z, its intersections, the two successive pullbacks, and the composite lifting argument; each cited model-category fact is stated by a cited node.
- Step 5: checked the Yoneda evaluation description, identification with the Segal map, m=0 and m=1 identities, m≥2 Segal hypothesis, interval intersections, and the final two-out-of-three argument against Rezk §4.1/Lemma 10.1.
- Step 6: checked the application to the original finite family, including nonconsecutive ambient faces, the empty family, and a singleton vertex family.
- New nodes: none; therefore B1–B7 and duplicate-node checks have no new-node cases. Existing dependency statements were opened and their quoted excerpts in `citations.json` were checked verbatim.
- Mathlib/source searches: the recorded LeanFinder, Loogle, LeanSearch, and grep searches were inspected; all hits are strict Segal simplicial-set declarations or unrelated results, so no Mathlib leaf is substituted.

Changes made: corrected the node's `created` record from the unrelated item/group to this item and NZ; corrected the source and proof-step places so Lemma 11.11 is described as an analogous gluing pattern rather than the exact theorem; retained the mathematical statement and six-step proof after checking the edge cases and dependency statements.
