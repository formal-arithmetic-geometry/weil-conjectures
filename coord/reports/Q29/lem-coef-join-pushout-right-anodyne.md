# Worker report: lem-coef-join-pushout-right-anodyne

## Files written

- `dag/nodes/sec-six-functors/lem-coef-join-pushout-right-anodyne.json`: statement, split into ten steps; no exact Mathlib match. Completed the earlier attempt rather than creating replacement nodes.
- `citations.json`: ten verbatim citation entries covering every node in every step's `uses`.
- `report.md`: this report. `searches.jsonl` holds the search command's actual log; the existing scratch script is not a delivery file.

New nodes: 0. New Mathlib leaves: 0. The item's statement, source, creation record, chapter, unit and blueprint ancestry are retained. No unit realization fields require changes: this helper is not its unit's key statement. No Lean was written or compiled, no agent was started, and nothing was pushed.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and for right-anodyne, join-pushout, simplicial-join and anodyne terminology, and checked `dag/lean_names_upstream.json`. There is no declaration stating this item. The master checkout was read only as reference, with the same absence of a relevant declaration; no master sorry declaration was treated as a finished proof.

## Literature wanted

WANTED: Jacob Lurie, *Higher Topos Theory*, Lemma 4.2.3.5 (Joyal), printed p. 251, PDF page 269, for lem-coef-join-pushout-right-anodyne. An archival copy under `literature/` was not found. I read the available online PDF at https://people.math.harvard.edu/~lurie/papers/HTT.pdf (zero-based page 268; extracted lines 16035–16052). I also read Lemma 4.2.3.6 immediately below it to check the parent's application. No download or literature-tree change was made. The proof is therefore marked `proof_origin.by = agent`, with the unarchived source identified, as the standing brief requires. No Stacks tag states this ordered simplicial join/right-anodyne lemma; the source place explicitly records that fact rather than assigning an unrelated tag.

## What was wrong or incomplete

The repository item was statement-only. The earlier sandbox attempt already expanded the saturation argument, but lacked its required report and accepted dry run. On checking the citations, I found that its Step 7 used the union-of-proper-faces definition of a boundary without citing a statement that provided it. `def-cbc-enhanced-diagrams-cones` gives the simplex and horn definitions but does not give the boundary definition. I added `lem-coef-kan-quillen-right-proper` to that step and included its opening definition sentence in the verbatim quotation. I also made the smallness sentence in the coproduct step explicit, eliminating the unnecessary suggestion of a universe enlargement.

There is no statement dispute: the inclusions, the weak homotopy equivalence hypothesis on the second inclusion, and the right-anodyne conclusion agree with HTT 4.2.3.5. No Kan or quasicategory assumption is used. The four original objects remain arbitrary small simplicial sets.

## Blueprint and reuse search

I read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-biduality-general.json`, the three levels in SETUP.md, and the current blueprint proof `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. Paragraph 2 is the coefficient-adjunction mapping-complex calculation that is the retained ancestor of this helper. The item's inherited long ancestry is preserved; this split implements the HTT 4.2.3.5 input used in the second inclusion of HTT 4.2.3.6 by `lem-coef-contractible-join-right-anodyne`, without changing any geometric unit step. The literal biduality unit has no proof steps for this technical helper to rebind, and I changed no maintainer-owned metadata.

`tools/blueprint_refs.py ancestor lem-coef-join-pushout-right-anodyne` returned `prop-coef-integral-exceptional-adjoint`. Blueprint searches for the item id, `right anodyne`, `pushout join` and `weak homotopy equivalence` found no matching imported node. A broad `join` search and whole-DAG searches for HTT 4.2.3.5 and join/right-anodyne terminology were also read. The most relevant existing results are the parent contractible-factor join lemma, `lem-coef-infinity-pushout-join-saturation` (inner-anodyne join saturation, not right-anodyne saturation), and `lem-coef-infinity-right-anodyne-saturation` (a product construction, not a join construction). Their statements do not state this item; I did not use their proofs as unstated stronger results. No new node is required, so there are no new/existing same-tag pairs to distinguish. `blueprint.same_as` remains `[]`.

## Mathlib search

The item's existing searches are preserved. I ran fresh logged searches through `msearch.py`: LeanFinder for the Leibniz join with an acyclic monomorphism, a second phrasing about the boundary/horn vertex shift, Loogle for `"anodyne", SSet`, LeanSearch for the ordered boundary/horn pushout join, and source grep for exact join/right-anodyne words and for the anodyne-class/horn-generator declarations. The JSON records use the exact logged tool and query and actual result summaries; no search was inferred or invented. All these services responded successfully in this pass.

I read the candidate sources `Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean`, lines 35–85, and `AnodyneExtensions/Basic.lean`, lines 58–105. `J` at line 46 includes every horn, and `horn_ι_mem_J` at line 49 permits every missing vertex. `anodyneExtensions` at line 72 is the lifting class against all-horn fibrations. The returned closure instances concern this all-horn class. Other hits were low-dimensional horn pushout squares, inner-horn fillers, cofibrations and monomorphisms. None states an ordered join construction with a right-horn conclusion, or gives it by one-line specialization. The exact join/right-anodyne grep had zero hits. The item remains split, not a Mathlib leaf.

## Review by Q29

I checked delivery-errors B–E with the node, its four cited statements, and HTT 4.2.3.5 open. The source gives the same two saturation reductions and shifted horn as this split. The extra degreewise arguments supply the closure details that the printed proof suppresses. I checked those details rather than treating the source's saturation assertion as an uncited black box.

Step 1 cites `def-weil-pbc-simplicial-set`, whose statement explicitly defines simplicial sets as functors and maps as natural transformations. In each mixed summand the domain is the union of two subsets, and their intersection is the product of the two smaller coordinates. Pure summands intersect in the respective smaller factors. A compatible pair of maps therefore gives a unique map on the union. Degreewise colimits inherit operators on representatives and their universal property is checked degree by degree. These are direct set and functor calculations, not an appeal to an uncited colimit theorem.

Step 2 cites `def-coef-infinity-right-anodyne`. Its statement contains isomorphisms and retract closure. The join formula makes the construction functorial on arrow squares, so sections and retractions remain sections and retractions. An isomorphism in either argument fills the entire mixed product. The argument also spells out why a retract of an injection remains injective.

Step 3 uses the same definition's pushout closure. The pushout along an arbitrary map, which need not be injective, has underlying set the new source disjointly unioned with the complement of the old source. The complement of the theta-domain is the product of the two complements in each mixed summand. The induced theta-square has that same complement on both sides and is therefore a degreewise pushout; the bijection is induced by the square, so is simplicial. This verifies both variables, including a noninjective attaching map, rather than assuming joins preserve every colimit.

Step 4 uses pushout and transfinite-composition closure from that definition. I checked the displayed intersection and union defining every successor of the P-chain, its two endpoints, and continuity: at a limit, a first coordinate belongs to an earlier stage, while the other joined subset is fixed. The pure second factor is present throughout. The injection-to-colimit assertion follows from equality being witnessed at a common later stage. Step 5 repeats these explicit checks for the Q-chain and second coordinates. Its pure first factor is present throughout. Both zero-length cases are identities.

Step 6 has no external cited fact: it deduces small coproduct closure from Steps 2–5 by replacing one summand at each successor in a small well-order. Each replacement is a pushout, and the limit is the degreewise union already described in Step 1. The empty family yields an identity. Thus coproduct closure is proved, not silently added to the definition of right anodyne.

Step 7 now cites both `def-cbc-enhanced-diagrams-cones` (monotone-map simplex and omitted-vertex horn definitions) and `lem-coef-kan-quillen-right-proper` (the boundary as the union of proper faces). I checked the simplicial isomorphism by splitting a monotone map at the initial vertex block. Membership in the union means omitting a first-block vertex or a second-block vertex other than p. For a pure second-factor simplex the nonempty first block supplies an omitted vertex; for a pure first-factor simplex there is a second-block vertex other than p because m is positive. Thus the domain is exactly the horn with p=n+1+k, in all dimensions including degenerate simplices.

Step 8 uses the right-horn generator range from `def-coef-infinity-right-anodyne`: 1 <= p <= n+m+1. The lower bound holds even when k=0; the upper endpoint k=m is permitted. In particular this is not an invocation of inner-anodyne generation.

Step 9 cites the actual statement of `lem-coef-kan-quillen-right-proper`, not a lemma hidden in its proof. That statement identifies cofibrations as degreewise injections and trivial cofibrations as retracts of horn-cell composites. Its weak equivalences are defined by realization, matching the item's definition exactly. Thus an injective weak equivalence is a trivial cofibration, and the second-variable closure already proved applies. No fibrancy hypothesis is inserted. Step 10 uses the same statement's boundary-cell description of every monomorphism and the first-variable closure. It then returns to Step 1's domain identification, giving every clause of the item. I checked that proof_deps is precisely the union of the uses and that every citation quote is a verbatim substring of the current cited statement.

The two elementary-definition nodes from other units are declared in split_report.tool_uses: simplicial functors and simplex/horn conventions are generic notions. The Kan–Quillen and right-anodyne nodes are in the item's own unit. No geometric unit route is replaced, no statement dependency was removed, and no forbidden SGA source was used.

For the small cases, n=0, m=1, k=0 gives Lambda_1^2 (edges 01 and 12), and k=1 gives Lambda_2^2 (edges 02 and 12), matching the direct join of a new first vertex with the corresponding endpoint and full second edge. For general m, k=0 gives the smallest shifted index n+1 and k=m gives the last horn. When either inclusion is the identity, the displayed map is an identity. If A is empty, so is A0, and both joins reduce to the second factor, again giving an identity. If B is empty, weak equivalence forces B0 empty and the map is an identity on A. If B0 is empty and B is nonempty, the weak-equivalence hypothesis fails on components, so this is not an overlooked allowed case. I also checked empty coproducts and zero-length and nonzero-limit chains. There are no new statements to test and no clause of this item was moved to another node.

## What remains

No mathematical subtask remains for the author. The second reader must independently review this sandbox and perform the delivery. The required remote dry-run result is recorded below when complete; no push is authorized in this pass.

## Second reading by Q29

I independently opened the item node, each cited node, the HTT PDF at Lemma 4.2.3.5, and the delivery-errors B–E guidance. The item statement agrees with HTT 4.2.3.5 hypothesis by hypothesis: arbitrary small simplicial sets, degreewise injective inclusions, weak homotopy equivalence only for the second inclusion, and the canonical ordered-join pushout map; no Kan or quasicategory assumption is present. The stated join formula and pushout/union identification agree with the degreewise construction.

- Step 1: checked against `def-weil-pbc-simplicial-set`; the functor/natural-transformation statement supports the degreewise union and colimit calculation, with the compatible-map argument written explicitly; verdict: elementary and sufficient.
- Step 2: checked against `def-coef-infinity-right-anodyne`; isomorphism, functorial-square, retract, and monomorphism arguments use only the stated saturated class and are spelled out; verdict: elementary and sufficient.
- Step 3: checked against `def-coef-infinity-right-anodyne`; pushouts along arbitrary maps are handled degreewise, including the complement-product calculation and both variables; verdict: elementary and sufficient.
- Step 4: checked against `def-coef-infinity-right-anodyne`; successor intersections, limit unions, injective ordinal colimits, endpoints, and the zero-length chain are explicit; verdict: elementary and sufficient.
- Step 5: checked against `def-coef-infinity-right-anodyne`; the second-variable chain repeats the needed calculation with its own coordinates and endpoints; verdict: elementary and sufficient.
- Step 6: checked against Steps 3–5 and the definition of right anodyne; well-ordering a small coproduct gives successive pushouts and degreewise limit colimits, including the empty family; verdict: elementary and sufficient.
- Step 7: checked against `def-cbc-enhanced-diagrams-cones` and `lem-coef-kan-quillen-right-proper`; the ordered simplex isomorphism, boundary union, horn omission criterion, pure summands, and all (n,m,k) endpoints give exactly (Λ_{n+1+k}^{n+m+1}); verdict: elementary and sufficient.
- Step 8: checked against `def-coef-infinity-right-anodyne`; (1\le n+1+k\le n+m+1) is the exact right-horn range, including (n=0), (k=0), and (k=m); verdict: elementary and sufficient.
- Step 9: checked against the full statement of `lem-coef-kan-quillen-right-proper`; its realization weak equivalences, monomorphic cofibrations, and horn-cell/retract description justify the second-variable reduction without fibrancy assumptions; verdict: non-elementary dependency stated exactly.
- Step 10: checked against `lem-coef-kan-quillen-right-proper` and Step 1; every monomorphism is generated from boundary inclusions, and the first-variable closure returns the displayed domain and conclusion; verdict: non-elementary dependency stated exactly.

There are no new nodes to audit under B1–B7. I searched the current DAG for every cited tag and for join/right-anodyne variants before retaining the existing nodes; no duplicate or Mathlib exact match states this ordered join theorem. The recorded Mathlib searches were rerun successfully (LeanFinder, LeanSearch, Loogle, and scoped grep), with no exact match. I checked small cases (n=0,m=1,k=0,1), general (k=0,m), identity inclusions, empty (A), empty (B), empty coproducts, and zero-length/limit chains. No statement dispute or source error was found, and no source or proof step required correction in this second reading.
