# Stage-1 report: lem-coef-kan-path-boundary-bijections

## Files written

- `dag/nodes/sec-six-functors/lem-coef-kan-path-boundary-bijections.json`: existing statement, split into eight proof steps. Statement and statement dependencies unchanged. Zero new nodes and zero new Mathlib leaves.
- `citations.json`: one entry per cited node per step, copied literally from that node's statement.
- `report.md`: this report.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` for the exact blueprint id and for based path, path fibration, boundary bijection, Kan/path and simplicial homotopy declarations. There is no declaration of the project stating the item. Mathlib's edge-path types, pointed-simplex multiplication witnesses, general model-category path objects and continuous homotopy groups do not constitute an attachment.

## Sources and wanted archives

WANTED: archival copy of Mark Hovey, *Model Categories*, https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf, printed pp. 81–88 and 97. I read it online: Theorems 3.3.1–3.3.2; Definition 3.4.4; the construction preceding Lemma 3.4.8 and that lemma's proof; Lemma 3.4.9; and Proposition 3.6.3 through its simplicial path-space comparison, before realization. The statement agrees with its simplicial part. No Stacks tag states this homotopy theorem. The generic monomorphism lifting input is Stacks Tag 08NM (`lemma-trivial-kan`), already present as a Mathlib leaf.

WANTED: archival copy of Kerodon Proposition 4.2.5.3, https://kerodon.net/tag/0153, which I read online to check the existing right-anodyne product node. This is a Kerodon tag, not Stacks Tag 0153.

I read the assigned chapter/unit records and the current `main-20261015` proof of `prop-coef-integral-exceptional-adjoint` as well as its older ancestor text. The relevant inherited ancestry is its second paragraph and displayed derived coefficient adjunction. This is a foundational simplicial sublemma reached through the frame and Kan-realization chain. No unit-level step or chapter route is replaced, and this item is not a unit's key node.

## Search and reuse

The whole-DAG search covered path fibrations, boundary bijections, simplicial homotopy, horns, anodyne products and prism filtrations. `tools/blueprint_refs.py search 'path fibration'` and `search 'boundary bijection'` both returned zero matching blueprint nodes; `ancestor` confirmed `prop-coef-integral-exceptional-adjoint`. Thus `same_as` remains empty. The existing `lem-coef-infinity-right-anodyne-product` is precisely the generic product input required here and belongs to this unit. The existing Mathlib leaf `lem-weil-pbc-trivial-kan-lifts-monomorphisms` supplies extension across a general monomorphism; no duplicate is created.

The item's inherited search records are preserved. I additionally ran and recorded two LeanFinder phrasings, qualified Loogle, LeanSearch and source grep. The first unqualified Loogle query had an unresolved identifier and the first grep used an incorrect subdirectory prefix; neither is used as evidence of absence. The qualified Loogle returned pointed-simplex multiplication laws, and the corrected grep returned only `KanComplex/MulStruct.lean` lines 8,31,33,45,57. I read that file through line 180 and `Path.lean` lines 1–45. These define pointed simplices and finite directed edge paths, respectively, and do not prove the target's path-fibration boundary bijection. All newly recorded queries were actually run with the mandated `msearch.py` command.

## Corrections and limitations

There is no statement dispute. The imported statement is kept verbatim, including the initial-endpoint convention for the degree-zero boundary and its claim only about pointed sets.

My initial dependency choice, the general `lem-coef-sset-anodyne-pushout-product` leaf, created a cycle because its statement references the Kan-Quillen theorem which depends on this item through realization. I removed that citation and instead used the existing right-anodyne product theorem, explaining the order-reversal reduction for initial horns. The final proof does not invoke the Kan-Quillen model structure, realization, or a theorem that depends on this item. This unnecessary statement-dependency cycle in the general leaf is a maintenance observation, not a change to that node.

My first injectivity paragraph was insufficient: trivial kernel of a pointed map alone does not prove its injectivity. I replaced it, and the vague prism triangulations, by a fully specified simplicial set `V_n` of lifts. Each of its two projections lifts against every boundary, which gives genuine bijections on all edge-generated components. This proves independence, surjectivity and injectivity at once, without assuming an unproved group structure or exactness stronger than the source states. The proof is marked `by: agent` because this parameterized two-projection argument is written here, although checked against Hovey's construction.

Nothing mathematical is left unfinished. All required work is in the existing item; no new statement-only node is necessary. No Lean was written or compiled, and no delivery was pushed.

## Review by Q18

I read the source places above and every statement actually cited: `def-cbc-enhanced-diagrams-cones`, `lem-coef-infinity-right-anodyne-product`, `def-weil-pbc-trivial-kan-fibration` and `lem-weil-pbc-trivial-kan-lifts-monomorphisms`. Each citation below uses the stated assertion, rather than an argument from its proof.

Step 1 uses the product theorem's exact right-anodyne conclusion for a right horn and any monomorphism. I verified the horn indices: the theorem covers `i>0`, including the last horn; initial horns are transferred by the explicitly defined involution `alpha^R(k)=s-alpha(r-k)`. This reverses all horn indices and preserves degreewise products, unions and monomorphisms. A Kan fibration and its reversal fill all horns. The passage from generating right horns to their saturated class is proved by successive fillers, colimits at limits, and the retraction equations. This avoids any hidden model-category axiom.

Step 2 translates the endpoint-pair lifting square to its exact union inside `I x Delta^n`. The needed leg is the monomorphism `boundary I -> I`, and the other leg is a horn, so step 1 applies to `K -> point`, whose horn lifting is precisely the cited Kan definition. Pullback lifting gives `q`; filling the base horn and then lifting gives the Kan property of the total space, while a constant base simplex gives it for the fibre. No nonemptiness of an arbitrary Kan complex is used.

Step 3 uses the endpoint `{0}=Lambda_0^1`, not `{1}`, in the boundary-by-interval product. The extension fixes that endpoint, so it stays in `P_xK`. At dimension zero the constant path is an explicit filler. This checks the complete boundary-lifting assertion, rather than just weak contractibility.

Step 4 uses the cited internal-functor definition to specify all simplices and operators of the comparison span. The boundary of the last face lies in the last horn; when `n=1` it is empty. Hence `r` really lands in the loop-fibre mapping simplicial set and `C_0` is exactly the loop fibre. These are elementary subfunctor and restriction constructions, not additional unproved theorems.

Step 5 uses the product theorem with `Lambda_n^n -> Delta^n` and `boundary Delta^m -> Delta^m`. I checked all overlaps: the top family's horn restriction is `e`, its projection is the prescribed base family on the parameter boundary, and that base family is `x` on every simplex boundary. The filler is therefore in `V_n`. This gives boundary lifting for `s` even for `m=0`, and exactly the representative lift required in the statement.

Step 6 uses the boundary-lifting property of `E -> point` already proved in step 3. The trivial-Kan definition also requires vertex-surjectivity; that is supplied by `m=0`, so the hypothesis of the monomorphism-lifting leaf is satisfied. The union `L` is a simplicial subset of the product, hence degreewise injective. The loop family on the last face and constant values on the other faces agree on intersections, as do the parameter-boundary values. The leaf therefore extends exactly this glued map. Its projection to `K` has constant boundary, which is the remaining condition in `V_n`. This proves boundary lifting for `r` with no assumption on its interior projection.

Step 7 proves directly that boundary lifting implies a bijection on vertices modulo edge chains: lift vertices, then each edge with both chosen endpoints. In particular it proves injectivity for every component, not just for the distinguished one. Vertices/edges of the mapping sets are precisely the representatives/generating homotopies in the question, so `c(r)c(s)^{-1}` has the required domain and codomain. Any prescribed-horn lift represents a vertex in the same `s`-component; this establishes both kinds of independence. No comparison with continuous homotopy groups or simplicial group law is needed.

Step 8 checks strict commutation with both projections under postcomposition and then takes the inverse of a bijection of sets. For `n=1`, the horn is `{1}`, and `d_1 gamma` is the initial vertex of the lift ending at the constant path; this verifies the source's convention explicitly. Constants supply the distinguished points.

I tested the small cases: a one-point or discrete Kan complex gives singleton based path and loop data; `j=0` has `C_0=F` and retains the entire fibre component set; an empty Kan complex has no vertex `x`, so the hypotheses cannot accidentally assert it is pointed. For the nerve of a one-object group, the based path space is the contractible groupoid of arrows starting at its object, the loop fibre is discrete on group elements, and the last-face rule sends a loop to its inverse under the usual edge convention. This is a natural pointed-set bijection as claimed and explains why no sign or endpoint swap may be silently imposed. Arbitrary higher parameters are handled by the two lifting squares, rather than by assuming that a topological triangulation produces a simplicial homotopy on the original simplex.

Delivery-errors B–E were checked against the final files: no new or duplicate nodes, no unsupported statement change, all notions defined inline or by the existing definition, no clause transferred to a helper, exact cited hypotheses and literal quotes, no cycle in the chosen foundations, and an explicit proof of the claimed compatibility. The earlier mechanical pass was followed by this mathematical repair; the required full dry run is rerun on the final packet before handing it to the second reader.

## Resumed worker verification and dry run

I rechecked the existing attempt against the current shared node, the assigned chapter/unit records, the current main-20261015 ancestor proof, and delivery-errors B–E. The shared item is still unsplit; its statement and ancestry agree with the sandbox. Fresh exact-id and mathematical-name searches of the read-only slopmaster2 project found no attachment. The saved searches.jsonl confirms that the additional Mathlib queries in this packet were actually run, including the two unsuccessful query attempts explicitly identified above. No new node or new Mathlib claim is introduced by this resumed review.

I reread Hovey Theorems 3.3.1–3.3.2, Definition 3.4.4, the boundary construction preceding Lemma 3.4.8, and the simplicial portion of Proposition 3.6.3 online, together with Kerodon Proposition 4.2.5.3 and Stacks simplicial.tex, definition-trivial-kan and lemma-trivial-kan (08NL/08NM). These confirm the initial-endpoint path space, the last-face boundary convention, the product lifting input, and the extension across the union in step 6. In particular, the two projections in steps 5–6 prescribe different data: the first fixes the interior projection to K, while the second leaves that interior free and extends into E. This distinction validates both squares and the component-bijection argument of step 7. I found no further mathematical correction necessary.

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q18 lem-coef-kan-path-boundary-bijections --no-push` printed `OK (not pushed) deliver/Q18/lem-coef-kan-path-boundary-bijections at fa7b4cdade: preflight passed`. The final report is included in a further dry run before handoff. This worker leaves the packet in the sandbox for the independent second reader and does not push it.

## Second reading by Q18

- Item statement: checked against Hovey, Theorems 3.3.1–3.3.2, Definition 3.4.4, Lemma 3.4.8 and Proposition 3.6.3 (simplicial part before realization); all hypotheses, endpoint conventions, the $j=0$ clause, and naturality agree.
- Step 1: checked against `lem-coef-infinity-right-anodyne-product`; the positive-horn pushout-product and the explicitly written order-reversal argument supply all horns. Verdict: sound.
- Step 2: checked the endpoint evaluation square and pullback definition of $P_xK\to K$ against the internal-functor definition and the cited product theorem. Verdict: sound.
- Step 3: checked the initial-endpoint boundary product (including $m=0$) against the path-space construction; the initial horn is covered by Step 1's reversal. Verdict: sound.
- Step 4: checked the definitions of $B_n$, $C_{n-1}$ and $V_n$, restriction along the last face, and the $n=1$ empty-boundary case. Verdict: elementary and sound.
- Step 5: checked both overlap compatibilities and the relative last-horn product lift against `lem-coef-infinity-right-anodyne-product`; the $m=0$ representative lift is present. Verdict: sound.
- Step 6: checked the glued map on $L$ and its extension using the exact statements of `def-weil-pbc-trivial-kan-fibration` and `lem-weil-pbc-trivial-kan-lifts-monomorphisms`; the latter is an off-unit generic tool and is now declared in `split_report.tool_uses`. Verdict: sound.
- Step 7: checked the two-line boundary-lifting-to-component-bijection argument and the identification of vertices and edges with the stated simplicial homotopy relations. Verdict: elementary and sound.
- Step 8: checked strict naturality under postcomposition and the $n=1$ last-face convention. Verdict: elementary and sound.
- New nodes: none; therefore B1–B7 and duplicate-node checks are vacuous. Existing definition and lemma statements were read verbatim in `citations.json`; no Mathlib or source-repository attachment was found.
- Small cases: checked the one-point/discrete Kan complex, $j=0$, $n=1$, and the absence of a vertex for an empty Kan complex; no statement correction is required.

Changes made in this second reading: declared the cross-unit trivial-Kan extension lemma as a tool use for Step 6, and appended this independent statement/step/source audit. No mathematical statement or proof step required alteration.
