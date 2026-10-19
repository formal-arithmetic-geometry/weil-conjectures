# Stage-1 delivery: lem-coef-infinity-fixed-boundary-functor-kan

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-fixed-boundary-functor-kan.json`: existing statement, split into six complete horn-filling steps; no Mathlib match for the whole statement.
- `citations.json`: one verbatim statement quotation for each node used by each step.
- `searches.jsonl`: actual msearch records for this item; the node retains the prior worker's searches and appends the five searches run here.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The proof reuses the existing Mathlib leaf `lem-coef-infinity-inner-fibration-corner` and the existing split `lem-cbc-invertible-prism-extension`.

## Attachments

None. Searches of the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the blueprint id, fixed-boundary terminology, boundary/Kan terminology, and quasicategory/Kan terminology gave no declaration stating this item. The exact upstream master source was also checked as reference material, not as evidence of completion. No Lean was written and no compiler or build tool was run.

## Wanted sources

WANTED: archived Kerodon, Proposition 4.6.1.11, Tag 01P1, for lem-coef-infinity-fixed-boundary-functor-kan.

WANTED: archived Kerodon, Proposition 4.1.4.1, Tag 01BT, for the inner-fibration corner input of lem-coef-infinity-fixed-boundary-functor-kan.

WANTED: archived Kerodon, Lemma 4.4.4.8, Tag 01DP, for the absolute outer-horn prism input of lem-coef-infinity-fixed-boundary-functor-kan.

I read 01P1 and the whole statement and proof of 01DP online. These are Kerodon tags, not Stacks tags. No Stacks statement or archived literature in this repository states this specific quasicategorical fixed-boundary result. The proof is therefore marked agent-written, with the online sources precisely identified; no document was downloaded or written into the read-only literature directory.

## What needed correction

The imported statement is correct and unchanged. It agrees hypothesis by hypothesis with 01P1: a quasicategory X, any small B, a simplicial subset A containing all vertices, an arbitrary map f on A, and the literal strict fiber, possibly empty.

The node had no proof. Kerodon's proof of 01P1 invokes restriction as an isofibration (01F3), but the DAG node for that theorem, `lem-coef-infinity-isofibration-exponentiation`, already cites this item in its Step 4. Citing that parent would be circular. I followed the explicitly retained route documented in the item's source and the parent's review: inner corner, absolute prism, and opposites. The proof does not use the parent, pointwise detection, the relative equivalence prism, a pinch comparison, or an equivalence-reflection theorem.

The chapter and unit records were read. This item is a foundation below the derived Hom / derived limit calculation in paragraph 2 of `prop-coef-integral-exceptional-adjoint`, not the unit's key statement. Its blueprint ancestry, chapter and unit are retained. No unit record needs editing. The absolute prism is declared as a generic tool use because it is filed in the smooth-purity unit; no geometric argument or proof route is replaced. No prohibited SGA source is used.

## Unfinished work

None within the one-level split. The two theorem inputs already exist. This delivery introduces no statement-only prerequisites.

## Not duplicates

No new nodes. Whole-DAG searches for 01P1 and fixed-boundary/vertex terminology and blueprint searches for `fixed boundary`, `fixed-boundary`, `horn`, and `Kan complex` were read. Only the item itself and its parent mention 01P1; the parent's relative mapping-space fibration theorem is not a replacement proof of this item. The existing corner leaf states exactly the inner-lifting tool required. The prism node is already the needed general outer-prism input. Thus no duplicate was created.

## Review by NS

I read the worker brief, stage-1 contract, three levels and tool-use rule in SETUP.md, delivery-errors B through E in full, GOAL.md, dag-sync.md, the chapter and unit records, the blueprint ancestor's original proof, the parent split and its review, and the full statements of every cited node. I compared the item directly with Kerodon 01P1 and checked the prism input against Kerodon 01DP. There are no new-node sources to review.

For Step 1, `def-cbc-enhanced-diagrams-cones` explicitly defines the internal functor simplicial set, its simplicial operators, and degreewise products and pullbacks. I wrote both transposition formulas rather than silently appealing to an enriched adjunction: evaluate a_m(t) on (b,id), and recover it by restriction along id_B times t. Naturality gives the simplicial map, and the two maps on the union agree on A times the horn. This is degreewise gluing and definition expansion, not an uncited extension theorem.

For Step 2, the same definition gives the simplicial operators and the fact that a horn in dimension one is one endpoint. The degeneracy of the supplied vertex fills either one-dimensional horn. This neither chooses an extension of f nor assumes that the fiber has a vertex before a horn is supplied.

For Step 3, I opened `lem-coef-infinity-inner-fibration-corner`. Its statement allows any degreewise injection i and any inner fibration p, without an extra fibrancy assumption. Here the actual inclusion A into B is degreewise injective and p is X to a point, whose inner lifting is precisely the quasicategory hypothesis. Its displayed corner identifies with restriction because internal functor sets into a point are points. The lifting square has the constant n-simplex at f below it, so the filler stays in the strict fiber. I also read its Mathlib match `SSet.innerFibration_pullbackObjObjπ`, Inner/PushoutProduct.lean:70-90: this is the same corner and genuinely supplies inner lifting, not the outer-horn assertion being proved.

For Step 4, I opened `lem-cbc-invertible-prism-extension`. It allows arbitrary A subset B and arbitrary small B, requires n at least 2, and extends a map on exactly the union in Step 1 if all vertex edges [0,1] are equivalences. All vertices of B are in A, so the whole vertical simplex at each vertex is constant; the distinguished edge is the degenerate identity with degenerate inverse witnesses. I checked that [0,1] is present in the initial horn even at n=2. The conclusion extends all of the A product, not just its vertices, which is essential for the strict boundary equation.

For Step 5, I checked the explicit reversal formula alpha_rev(j)=s-alpha(r-j), including identities, composition and involutivity. It fixes the degreewise vertex sets, preserves unions and products, and exchanges omitted vertex i with n-i under the displayed representable identification. Therefore inner horns stay inner, the final horn becomes the initial horn, and X_op is a quasicategory by reversing its inner-horn problems. Reversing f times the projection still gives f_op times the projection. The prism statement is applied to B_op and X_op, with every vertex edge again an identity, and applying the involution again gives exactly the original boundary data. This is one explicit reindexing calculation; it contains no separate comparison theorem hidden as a long step or a new restatement of the item.

For Step 6, the definition node says the Kan condition only concerns n at least 1 and imposes no nonemptiness condition. Every such horn has a vertex, so an empty fiber has no input horn. I checked B empty (the point), A=B (the unique constant extension, again a point), B a discrete simplicial set (A=B), and B=Delta^1 with A its boundary and X the nerve of a category (the fiber is the discrete set of arrows with the two chosen endpoints, including an empty Hom set). The all-vertices hypothesis is necessary: without it, A empty and B a point gives X, and the nerve of the noninvertible arrow category is not Kan. These tests reveal no missing hypothesis and require no statement dispute.

For C1/C4, citations.json quotes the exact statement parts actually used; no proof-only construction is borrowed. For B/D, no new nodes were created, no clause was moved to a renamed node, and every case of the desired lifting problem is solved in the item. For C6 I computed the full dependency closures of the definition, corner leaf, and prism (4, 5, and 11 nodes respectively): none reaches this item. All six proof steps are shorter than 2000 characters (961, 346, 729, 737, 1335, 419); I also read each for hidden hypotheses and lemmas. The only non-elementary inputs are precisely the corner leaf and the absolute prism.

I ran the required Mathlib search command with leanfinder, loogle, grep, leansearch, and a second leanfinder phrasing, and read every hit. Basic.lean:35-55 only gives the definitions and Kan implies quasicategory. StrictBicategory.lean:14-67 uses homotopy categories of internal Homs; it does not prove this strict fiber Kan. Coskeletal.lean:53-80 constructs ordinary right Kan extensions under StrictSegal. None states this item or a one-line generalization. The existing searches are retained as inherited records; I did not invent or rewrite any search result.
