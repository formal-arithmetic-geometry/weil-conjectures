# Stage-1 worker report

## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-prism-extension.json: item split into six steps; imported statement preserved verbatim; no complete Mathlib match.
- citations.json: 18 verbatim step/node quotations, covering every proof citation.
- report.md: this report. searches.jsonl contains the actual search-command log, including the earlier attempt and eight fresh searches.

No new DAG nodes or Mathlib leaves were created.

## Attachments

None. Fresh searches under /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact id, blueprint tag, prism, inner-fibration and outer-horn terminology found no candidate declaration. The read-only upstream master search likewise found no exact tagged/prism declaration. No Lean audit on this item exposes an unattached open declaration. No Lean was written or compiled.

## Wanted sources

WANTED: archived Kerodon Proposition 4.4.5.8, Tag 01NX, for this item.
WANTED: archived Kerodon Lemma 3.1.2.12, Tag 00TH, for the reused right-prism filtration.
WANTED: archived Kerodon Proposition 4.4.2.13, Tag 01H0, for the reused relative final-outer-horn lemma.

I opened and read all three tagged pages online. No source was downloaded. The proof_origin remains agent because no archived source in literature/ is available, and the skeletal/quotient and dual arguments are explicit expansions. These are Kerodon tags, not identically spelled Stacks tags. No SGA source is used.

## What was wrong or incomplete

The live item was unsplit. Its all-vertices-equivalences hypothesis is valid, and is deliberately stronger than the endpoint condition in 01NX. The earlier sandbox attempt changed it to the weaker endpoint condition, which is mathematically true but unnecessary and not authorized by a false imported statement. I restored the live statement verbatim and adjusted Steps 3 and 6 to use that actual hypothesis. No STATEMENT-DISPUTED issue remains: the imported statement has no counterexample or typing defect.

The earlier attempt proposed an outer-horn child that already exists as lem-cbc-inner-fibration-equivalence-outer-horn-lift. There is no such new file in the sandbox. The item cites the existing relative result directly; an absolute outer-horn theorem would not suffice. I declared this cross-unit generic tool in split_report.tool_uses. The right-prism node is now in the same unit, so it needs no off-unit declaration.

## Source error

The online 01NX proof omits the equation over the prescribed base from its intermediate ordered pairs and displays a point in a lifting square where the base is required. Our H_n invariant and every finite filler explicitly retain the prescribed base equation. The source theorem statement is unaffected.

## Unfinished work

None in this one-level split. The existing unsplit outer-horn dependency remains its own downstream item. The present worker performs only the required --no-push dry run; a fresh second reader owns delivery.

## Not duplicates

No new node remains. The proposed earlier outer-horn child duplicates the final-horn clause of lem-cbc-inner-fibration-equivalence-outer-horn-lift and was removed before this turn. Fresh whole-DAG searches by 01NX and prism terminology, and blueprint_refs searches for prism and inner fibration, found no imported blueprint statement matching this item. The absolute invertible-prism theorem cannot replace the relative prescribed-base assertion. The parent isofibration-exponentiation node applies this item after adjoining all missing vertex lifts; it does not state the item.

## Mathlib searches

I ran eight fresh msearch commands: grep over AlgebraicTopology, Loogle, LeanSearch, and differently phrased LeanFinder searches, including reruns of the three inherited queries absent from this sandbox log. All eight searches returned successfully. The exact query strings and digest records are copied from searches.jsonl into the item, with no invented searches. Returned candidates were read in the pinned source: InnerFibration.lean:29-103, RelativeMorphism.lean:34-97, CategoryWithFibrations.lean:35-100, AnodyneExtensions/Inner/PushoutProduct.lean:54-85, Localization/Predicate.lean:375-382, FiberedCategory/HasFibers.lean:151-159 and SimplicialSet/NerveAdjunction.lean:50-63. They describe inner horn lifting, stronger Quillen all-horn lifting, homotopy records, internal-Hom inner fibrations, ordinary-category lift transport, or truncated strict-Segal constructions. None states this relative extension result or specializes to it in one line. Earlier actual search records remain intact.

## Review by Q24

I read delivery-errors B through E in full, the worker brief and role, the stage-1 rules, SETUP's three levels, GOAL, dag-sync, the chapter and unit records, the current main-20261015 ancestor and the historical master proof, and the parent isofibration-exponentiation statement and proof. The current ancestor file moved to sk-thm-sf-package and has no proof text; the historical derived Hom/limit paragraph supplies the inherited provenance. The inherited unit and ancestry are retained. This item supplies coherent diagram infrastructure below the unit, and changes no geometric coefficient category or base-change map.

For sources I read 01NX's full statement and proof for the item, 00TH's full filtration and vertex formula, and 01H0's prescribed-base final-horn result. The all-vertex hypothesis implies 01NX's final-vertex condition, and survives taking opposites. For the relative skeletal dependency I read its complete statement and verified its existing Mathlib match SSet.relativeCellComplexOfMono in Skeleton.lean:428-446: the pushout cells are all nondegenerate simplices outside A, including the stated dimension-zero case. There are no new-node sources to audit.

Step 1 cites the enhanced-diagram definition for degreewise products, the colimit definition for gluing on the union, and the boundary-cell leaf for the actual relative filtration. All three statements were opened. Every vertex lies in A, so the zero-cell index is empty and Z_1=A. H_n is explicitly over g and agrees with both pieces of h_0. Every later choice is indexed by a small set; no large colimit existence theorem is invoked.

Step 2 cites those same definitions and the full right-prism statement. The latter supplies the exact sigma_q maps and pushout horns Lambda_(q+1)^(n+1); its statement, not just its proof, includes these data. The cell characteristic map comes from the boundary-cell pushout, so it is not assumed injective. For q<n the index is strictly inner, making the item's own lifting hypothesis applicable over the actual simplex g_tau sigma_q. Pushout uniqueness proves the base equation after gluing.

Step 3 cites the standard-simplex definition to compute the entire final edge from its endpoints, the prism formula for sigma_n, the colimit definition for the last gluing, and the existing relative outer-horn statement. I verified the latter states the final-horn clause with both exact equations, source and target quasicategories, inner fibration, dimension at least two and equivalence in the source. Here the dimension is n+1>=2, and sigma_n sends its last two vertices to (0,n),(1,n). The all-vertex hypothesis supplies precisely the needed prescribed equivalence at tau(n), already in A and in the boundary. The common simplicial-set universe convention supplies the smallness in the dependency; there is no additional finiteness, Kan, or isofibration assumption.

Step 4 cites the degreewise-product and colimit definitions and the same boundary-cell pushout. Its explicit quotient construction checks agreement on every boundary identification and checks simplicial operators on representatives. This proves the required gluing without citing a nonexistent general product-preserves-colimits theorem. It handles identified faces and repeated vertices. The given endpoint and the prescribed base equations are checked on every summand.

Step 5 cites the relative filtration's stated colimit and both definitions. The degreewise union has the colimit property by the written compatibility argument; uniqueness of colimits identifies it with B. The h value is independent of stage, and simplicial operators stay in the chosen stage. Both required equations follow on every element, including infinite-dimensional B. This step proves the assembly rather than moving it into a child node.

Step 6 cites the simplex/horn/equivalence definitions and writes the opposite involution on every operator. Reversal respects composition and squares to the identity, carries missing vertex i to s-i, preserves inner horns, and swaps the interval endpoints. Reversed inverse edges and reversed witness triangles remain inverse witnesses. The all-vertex equivalence hypothesis is preserved. Applying the already proved epsilon=1 case and reversing back proves epsilon=0 with exact restriction and base equations. This explicit calculation is not hidden in a general transport assertion.

Small cases checked: empty B has the unique empty extension; A=B already supplies the whole map; a discrete B forces A=B. A first missing one-simplex attaches a square using an inner two-horn followed by a final two-horn whose final edge is the prescribed equivalence. The final-horn result's minimum dimension is exactly two, so dimension one is never misapplied. Empty source quasicategory forces the prescribed vertex data empty and creates no nonemptiness assertion. Arbitrarily many cells and identified simplex vertices are included in the quotient and union construction. Each non-elementary imported input is one of the cited statements; direct quotient and opposite calculations are written in the steps. No helper merely restates a clause of the item.

I checked B's standalone-statement/source/search/blueprint requirements, C's statement-versus-proof distinction and exact citations, D's no-restatement and induction requirements, and E's source/base/dimension/equivalence hypotheses and small cases against the actual node files. All 18 citation quotes are literal substrings of the cited statements. proof_deps equals the union of uses. The main correction in this turn was undoing the earlier unwarranted generalization and replacing the earlier report's contradictory statement-change claims with this account.

## Validation

Required command: python3 /home/ubuntu/weil-launcher-nt/deliver.py Q24 lem-coef-infinity-equivalence-prism-extension --no-push .

Only the approved delivery wrapper runs maintainer preflight/check_dag/review_split on the server. No local maintainer checks, compiler, Lake, build, direct git command, live-project write or push is performed. Final READY is issued only after explicit dry-run OK.

## Second reading by Q24

- Step 1 checked against Kerodon 01NX and the statements of `def-cbc-enhanced-diagrams-cones`, `def-weil-pbc-category-colimit`, and `lem-coef-infinity-monomorphism-boundary-cells`; the union pushout, empty zero-cell stage, and relative skeletal induction data are stated and the verdict is correct.
- Step 2 checked against Kerodon 01NX and the full statement of `lem-coef-infinity-right-prism-boundary`; the pulled-back boundary map, actual prescribed base simplex, inner indices `0<q+1<n+1`, and pushout gluing are all justified; verdict correct.
- Step 3 checked against Kerodon 01NX and `lem-cbc-inner-fibration-equivalence-outer-horn-lift`; the final horn has dimension `n+1>=2`, its final edge is exactly the prescribed vertical edge at `tau(n)`, and both restriction and base equalities are supplied; verdict correct.
- Step 4 checked against the cited product, colimit, and boundary-cell statements and against the quotient construction in the text; boundary identifications, repeated vertices, operators, and both equations are handled explicitly; verdict correct.
- Step 5 checked against the boundary-cell colimit and the colimit definition; the compatible degreewise union is identified with `B`, and stage independence gives a simplicial map with the exact two required equalities; verdict correct.
- Step 6 checked against the enhanced-diagram definition and the opposite-simplicial-set calculation; reversal preserves operators, horns, endpoints, and equivalence witnesses, so the epsilon-zero dual follows with exact equations; verdict correct.
- New nodes: none. I checked the whole DAG for prism, inner-fibration, and equivalence-prism duplicates and verified that every cited dependency already exists; no node or Mathlib leaf should be added.
- Small cases rechecked: empty `B`, `A=B`, discrete `B`, `n=0`/`n=1` attachment behavior, and the minimum final-horn dimension. No counterexample or typing defect was found.
- Repair made: corrected the item provenance stamp from the parent `lem-coef-infinity-isofibration-exponentiation` and group `Q37` to this item and `Q24`; the proof and statement were unchanged. This fixes the split’s created-item metadata and leaves the worker review intact.
