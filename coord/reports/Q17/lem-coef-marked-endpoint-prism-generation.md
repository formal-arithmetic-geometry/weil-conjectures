# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-marked-endpoint-prism-generation.json`: existing statement node split in eight steps; statement unchanged; no Mathlib match.
- `citations.json`: nine statement quotations covering every citation in the eight proof steps.
- No new nodes, no new Mathlib leaves, and no unit edits. The relative boundary-cell Mathlib leaf is reused rather than duplicated. `make_split.py` and `check_finite_cases.py` are sandbox-only preparation and finite-case checks.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id and marked endpoint, prism and marked-anodyne terminology found no declaration stating this item. There is no Lean audit entry on the imported item to discharge. The upstream master checkout is not treated as finished evidence.

## WANTED

WANTED: Jacob Lurie, *Higher Topos Theory*, Proposition 3.1.1.5, printed pages 148–149 (PDF pages 166–167 in the online book, zero-based pages 165–166), for lem-coef-marked-endpoint-prism-generation; online PDF read at https://www.math.ias.edu/~lurie/papers/HTT.pdf, not archived under literature/. Definition 3.1.0.1 on printed page 146 supplies the marking convention. No download was made.

WANTED: archival copies of Kerodon Lemma 3.1.2.12 (tag 00TH) and Proposition 1.5.5.14 (tag 0077), for the two reused simplicial-combinatorics inputs. Both online pages were read. These are Kerodon tags, not the unrelated Stacks tags. No Stacks tag states the marked generator comparison. The colimit definition uses Stacks Categories, tag 002F, label `definition-colimit`, in literature/stacks-project/categories.tex.

## What changed and why

The original item was a statement-only auxiliary lemma. It is true as written, so its hypotheses, markings, endpoint orientation and conclusion were retained. Its existing blueprint ancestry already identifies Proposition 3.1.1.5's technical role below the finite-adjunction-diagram realization; this was retained and explained in split_report. Whole-blueprint searches for marked endpoint prisms and final marked horns gave no equivalent imported node. Searches of the whole DAG found the precise relative cell and right-prism filtration nodes, which are enough: no new combinatorial lemma is needed.

The proof now separates the two containments. Relative boundary cells reduce arbitrary monomorphisms to boundary prisms. The existing prism filtration supplies actual horn attachment maps, and their induced markings determine which attachments are inner horns and which is the final marked horn. In the other direction the proof adds final-edge markings by a pushout and constructs actual section/retraction maps. It checks their restrictions on every simplex and their preservation of all marked edges, rather than appealing to an unmarked retract. The one-dimensional horn is handled separately.

I read the existing unit sk-prop-sf-biduality-general and chapter sec-six-functors. This item is a technical descendant of prop-coef-integral-exceptional-adjoint, not the unit's key statement. The split follows the existing coherent diagram foundation branch and changes no unit or chapter route. Both substantive simplicial lemmas have this same unit. The colimit and simplex definition nodes are definitions, not alternate routes. No SGA source is used.

## Source error

The marked pushout assertion in HTT Proposition 3.1.1.5's retraction argument needs its n=1 case separated. In that case the horn is {1} and its final edge [0,1] is absent. In the minimally marked prism target, the bottom horizontal edge and diagonal are unmarked. Adding markings to its domain (the right vertical edge plus the top horizontal edge) cannot mark either of these other edges by a marked pushout. In the product with the marked simplex both are marked. Thus that intermediate pushout description cannot be used for n=1. The proposition and this item's statement remain true: the first final horn is already P(empty -> point). Steps 4 and 5 explicitly impose n>=2 only on the intermediate pushout argument, with n=1 proved separately, so no hypothesis was added to the item. This is a local source-proof correction below the unit route, not a statement dispute.

## Mathlib research

All new searches were executed with the mandated msearch.py wrapper and are recorded verbatim in searches.jsonl and the item's mathlib_searches. LeanFinder was queried with two phrasings, and LeanSearch, Loogle and marked-source grep were also run. They found only unmarked horns, unmarked boundary generators, terminality of the standard zero-simplex, and generic cylinder constructions. I read CategoryWithFibrations.lean:38–60, Horn.lean:42–67 and Skeleton.lean:428–446 in the pinned Mathlib checkout. The skeletal construction is exactly the existing Mathlib leaf SSet.relativeCellComplexOfMono; the unmarked horn hits do not state the marked generator comparison. Loogle and the targeted marked grep had no hits. The old item's search entries are preserved; new entries are copied from this sandbox's actual log.

## Not duplicates

No new nodes. The would-be boundary-cell input is precisely lem-coef-infinity-monomorphism-boundary-cells; the would-be prism-triangulation input is precisely lem-coef-infinity-right-prism-boundary. Both are cited directly. The marked refinements and retract computations belong in the item's steps, not in new nodes restating its clauses.

## Review by Q17

I read HTT Proposition 3.1.1.5 online together with the marking definition, Kerodon 00TH and 0077, and the statements and source records of both reused lemmas. The item's smallness and endpoint {1} agree with these sources, and the I and F markings agree exactly with HTT's classes (1) and (2). I also read Stacks categories.tex at definition-colimit for the universal property used in the elementary gluing checks. No new node statements require separate source verification.

Step 1 cites def-weil-pbc-category-colimit for the universal property, and def-cbc-enhanced-diagrams-cones for degreewise products and simplicial operators. I checked the marked colimit construction directly: mark images, then a map preserves those markings iff its input maps do. The product marking formula uses exactly the minimal marking in the second coordinate, so no arbitrary marked cofibration theorem is being assumed.

Step 2 cites lem-coef-infinity-monomorphism-boundary-cells. Its statement provides a filtration for every degreewise injective map, indexed by missing nondegenerate simplices; it does not just assert abstract saturation. Those are precisely the hypotheses and the cells used. The marked prism gluing is written out from the cell pushout and Step 1. A small well-order of each small cell set makes the coproduct attachment a small transfinite composite; countably many dimension stages still give a small ordinal. At dimension zero the vertical edge is genuinely new and is marked by the zero-dimensional prism. No presumption that a product preserves an arbitrary colimit, or that unmarked saturation implies marked saturation, is used.

Step 3 cites lem-coef-infinity-right-prism-boundary. Its statement supplies exactly X_0, the horn index q+1, the specific maps sigma_q and each pushout square; the proof uses none of its hidden construction. I checked the marking on sigma_q: its only nonconstant marked edge joins the two occurrences of q. For q<m this edge is already in the boundary part of X_0, and q+1 is an inner index. For q=m it is the final edge of the final marked horn. When m=0 the sole attachment creates the marked interval from its terminal endpoint. These statements establish the marked pushout squares, rather than borrowing them from the unmarked node.

Step 4 uses the horn definition in def-cbc-enhanced-diagrams-cones to identify the n=1 generator. This is a direct identification with P(empty -> point); it closes the small-case gap in the source proof. The n>=2 assumption introduced for Steps 5–7 is exhausted by this case split and is not a hypothesis of the item.

Step 5 cites that same horn definition and the colimit universal property. I verified that the final edge belongs to the horn for all n>=2 by its omission of vertex 0. Thus every newly added marking in D times M is already represented in D times H_E. This is exactly the condition needed for the displayed square to be a marked pushout. The assertion would fail in n=1, and Step 4 deliberately handles that case separately.

Step 6 uses the weakly increasing-map description in def-cbc-enhanced-diagrams-cones to construct the simplicial section and retraction from monotone vertex functions. The comparison-pair check establishes monotonicity even at (1,n-1). I checked all possible marked edges: constant second coordinate and the final edge with any allowed first-coordinate edge. Their images are degenerate or final. Thus no marking is forgotten. The left inverse is the identity on every vertex and consequently on every simplex by the stated precomposition model.

Step 7 again uses the actual horn criterion, which says a simplex omits a vertex other than n. The formula for r either keeps the omitted vertex or, on the top endpoint, omits n-1. This verifies containment degreewise even for degenerate simplices, so the restrictions define the required arrow-category maps. Markings are induced, hence Step 6 verifies preservation on those restrictions. The commutative squares are inclusions and restrictions of the same j and r, and their composite is the identity. Step 8 only applies the definition of generated closure to the proved containments.

For delivery-errors B, there are no new nodes or new leaf claims; every statement notion has a definition node or is defined inline, and TeX and blueprint fields were checked. For C, the nine quotations in citations.json are verbatim from the cited statements and match the uses just described. The two non-elementary inputs are cited statement-level results; the remaining steps are explicit set-level constructions, not uncited model-category results. For D, the argument lives in the item's steps and no auxiliary node repeats a clause or is used circularly. For E, I verified the only dimensional restriction exactly where the marked pushout requires it, the endpoint orientation, the shape of all products, and smallness of every indexing set. The finite-case script exhausts strict chains for prism dimensions m=0..5 and retraction dimensions n=2..6, checks the horn intersection, inner-stage marking availability, monotonicity, horn restriction and preservation of markings; arbitrary simplices are repetitions of those chains. It also checks the n=1 exception. Empty monomorphisms, identity monomorphisms, and the empty cell sets are included by the filtration argument (identity gives an identity prism map). The script printed OK. I corrected the source's n=1 intermediate-pushout issue before writing the final split.

## Unfinished work

None in this one-level split. No Lean, compiler, Lake or local project-checker command was run. The second reader should review the marked gluing and the explicit n=1 separation and perform delivery; this worker only runs --no-push.

## Second reading by Q17

- Source and statement: I opened HTT Definition 3.1.0.1 and Proposition 3.1.1.5 (printed pages 146 and 148–149) and checked the marked-set convention, endpoint orientation, the final-edge marking, all three class equalities, and the smallness quantifiers; verdict: agrees hypothesis by hypothesis.
- Step 1: I checked the degreewise marked-pushout and union claims against `def-weil-pbc-category-colimit` and `def-cbc-enhanced-diagrams-cones`; the minimal product marking is stated and used exactly; verdict: elementary and correct.
- Step 2: I read `lem-coef-infinity-monomorphism-boundary-cells`; its filtration supplies precisely the boundary cells used in the prism attachments, including the empty 0-cell case, and the transfinite serialization is small; verdict: cited statement suffices and the gluing argument is explicit.
- Step 3: I read `lem-coef-infinity-right-prism-boundary`; its exact horn preimages and pushout squares give the filtration used here. I checked the vertical marked edge at every inner stage and the final marked edge at the last stage, including `m=0`; verdict: cited statement suffices and markings are tracked correctly.
- Step 4: I checked the horn definition directly: `Lambda_1^1 = {1}`, so the `n=1` final generator is `P(empty -> Delta^0)`; verdict: correct case split with no added hypothesis.
- Step 5: For `n >= 2`, I checked that the final edge lies in the horn and that every extra target marking is already represented in `U`; the marked colimit universal property then gives the displayed pushout. The intermediate assertion is deliberately not used for `n=1`; verdict: correct, with the source proof's dimension-one gap repaired.
- Step 6: I checked the weak-chain description, monotonicity of `r` at the exceptional vertex `(1,n-1)`, `r j = 1`, and images of vertical and final marked edges; verdict: explicit marked section/retraction is correct.
- Step 7: I checked the restrictions in every simplicial degree: the image of `r` omits a horn vertex, including the cases where the omitted vertex is `n-1`, and the arrow-category retract squares commute; verdict: correct and not merely a vertex-level argument.
- Step 8: I checked both closure containments and the passage from boundary prisms to arbitrary monomorphisms; verdict: follows from Steps 2–7 and the stated closure operations.
- New nodes: none. I searched the DAG for the two combinatorial inputs and reused `lem-coef-infinity-monomorphism-boundary-cells` and `lem-coef-infinity-right-prism-boundary`; no duplicate or Mathlib leaf was created.
- Edge cases: I ran `check_finite_cases.py`; it printed `OK` for `m=0..5`, marked retractions `n=2..6`, and the `n=1` exception, while the filtration covers empty and identity monomorphisms; verdict: all are covered by the stated constructions.
- Delivery fields: citations are verbatim quotations for every cited step, `proof_deps` is the union of step uses, blueprint ancestry is populated, and no SGA source is cited; verdict: conforms to B1–B7 and C1–C5.

No file changes were needed after this reading; the only required addition was this second-reading record.
