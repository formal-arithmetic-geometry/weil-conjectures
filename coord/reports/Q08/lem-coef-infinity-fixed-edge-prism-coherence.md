## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-fixed-edge-prism-coherence.json`: statement node, split into seven steps; statement unchanged. No exact Mathlib match.
- `citations.json`: a verbatim statement excerpt for every citation of every proof step.
- `searches.jsonl`: actual Q08 search results. Existing Q70 Mathlib search records in the item were preserved, and the new Q08 searches appended.

No new nodes; no Mathlib leaves. The sandbox initially held only dispatcher markers, with no earlier split or report to recover.

## Attachments

None. Searched all of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id and for fixed-edge, prism, triangle-space, pinch, Quasicategory, coslice, CompStruct and mappingSpace terminology. The only broad-term source hit was an unrelated scheme approximation indexed by a coslice. No project declaration supplies this assertion. The upstream master checkout is not evidence of a completed proof and was not used as such.

## WANTED

WANTED: an archive of Kerodon Subsection 4.6.8, tag 01PF, specifically Construction 4.6.8.9, Notation 4.6.8.15, Proposition 4.6.8.16 with its proof, and Remark 4.6.8.17, for lem-coef-infinity-fixed-edge-prism-coherence. Read online at https://kerodon.net/tag/01PF on 2026-10-17. No archive was downloaded or written into the shared project. The proof is accordingly recorded as agent-written, with the local blueprint ancestor as its project source and online places on the steps. This is a Kerodon tag, not Stacks tag 01PF; no Stacks theorem is substituted for the quasicategorical statement.

## What needed repair

The imported item had an explicit and correct statement, but no proof. In particular, calling its roof a representative of precomposition requires that its left leg can be inverted. The statement's displayed class equality by itself does not establish that. Steps 2–3 now prove this: boundary lifting for r_1 is the single inner horn missing face 1, then existing trivial-Kan and left-pinch results give its homotopy inverse.

The degreewise prism map is verified as a simplicial map, including every degeneracy, by a formula for an arbitrary monotone indexing map. Each boundary is computed with its actual ordinal labels. The p-naturality claim is proved as equality of prescribed restrictions and prisms, without assuming that chosen homotopy inverses are strictly natural. No inner-fibration condition on p is introduced.

The current main-20261015 ancestor lives in `sec-six-functors/sk-thm-sf-package`, while this item's inherited historical ancestry and maintained unit remain `prop-coef-integral-exceptional-adjoint` and `sk-prop-sf-biduality-general`. I read the chapter and unit records and the main-20261015 proof of the ancestor, especially its paragraph 2 mapping-complex adjunction. This infrastructure supports that adjunction; it does not replace the coefficient argument or the unit route. No maintainer-owned binding or unit realization was changed. The ancestor's historical master proof path does not exist in this checkout, so proof_origin names the extant main-20261015 proof file instead. There is no blueprint_update on the item.

## Unfinished work

None in the split. The cited existing nodes retain their own proof obligations in the DAG. Stage 2, Lean writing and compilation are outside this delivery.

## Searches and reuse

Whole-DAG searches for 01PF, 4.6.8.16 and fixed-edge terminology found the existing mapping-composition and left-pinch nodes, as well as the cocartesian-mapping-criterion parent. I read their statements and reused them. Whole-blueprint searches with blueprint_refs.py for precomposition, triangle, pinch and prism gave no blueprint statement identical to the item; same_as remains empty. Ancestor lookup returned prop-coef-integral-exceptional-adjoint. No smaller fact needed a new node: the boundary-lifting and boundary-restriction calculations are explicit instances of the horn and left-pinch definitions.

The Q08 item searches used msearch.py with LeanFinder (two phrasings), Loogle, LeanSearch and a grep across AlgebraicTopology. I read the returned hits: CompStruct and CompStruct.map describe one 2-simplex, the truncated quasi-category operations compose individual edges, HornColimits describes individual low-dimensional faces, and RelativeMorphism describes general homotopy precomposition. None gives a natural map from the entire fixed-edge triangle simplicial set, all three boundary formulas and its comparison with the homotopy-class composition roof. Read CompStructTruncated.lean (definitions of Edge and CompStruct, initial 100 lines) and RelativeMorphism.lean (homotopy and homotopy-class precomposition, lines 130–195) to exclude superficially similar hits. The second phrasing returned HornColimits inclusions, which likewise concern a single specified horn face. Every recorded new query is an actual command result; no unavailable service is recorded as absence.

## Not duplicates

No new nodes are proposed. The item is stronger than an individual 2-simplex composition witness and addresses fixed-edge prism naturality, rather than the general existence/associativity of composition in lem-coef-infinity-mapping-composition or the left-pinch equivalence of lem-coef-infinity-left-pinch-comparison. Its parent cocartesian-mapping-criterion uses this result, so is not a possible dependency.

## Review by Q08

I read Kerodon 01PF, Construction 4.6.8.9 and Notation 4.6.8.15 to check the composition convention, then Proposition 4.6.8.16 and its proof for the prism and Remark 4.6.8.17 for invertibility of the roof leg. The source uses the edge-coslice model. In the item's explicit model, a simplex is precisely the edge followed by the constant terminal face; its two restrictions are the left-pinched spaces as actually defined by the existing left-pinch node. There is no change of endpoint convention. The source's prose preceding Proposition 4.6.8.16 calls these coslice models right-pinched, whereas its proposition and formulas use the left-pinch inclusions. I follow the actual formulas and the item's explicit definition, so this naming inconsistency has no effect on the statement.

Step 1 uses the standard-simplex/operator definitions in def-cbc-enhanced-diagrams-cones and the explicit constant-final-face definition in lem-coef-infinity-left-pinch-comparison. I checked that fixing 0 and 1, and then omitting either one, gives exactly the indexing maps fixing a single first vertex. This is a direct restriction calculation.

Step 2 uses the horn definition and quasicategory axiom in def-cbc-enhanced-diagrams-cones and the entire boundary-lifting definition in def-weil-pbc-trivial-kan-fibration. Faces with labels 2 through m+2 come from the boundary of the parameter simplex; face 0 comes from the prescribed image under r_1. Their union omits only face 1. I checked the special case m=0 separately: the missing boundary supplies no faces, but the already fixed edge s and the given y-to-z arrow supply the two inner-horn edges. The filler stays in T because the constant final face is contained in face 0. No general coslice comparison theorem or uncited saturated-class lifting theorem is used.

Step 3 uses the exact Kan-complex and homotopy-equivalence assertion of lem-coef-infinity-left-pinch-comparison. The statement of lem-weil-pbc-trivial-kan-lifts-monomorphisms genuinely allows an arbitrary degreewise injective map, so it applies to every horn inclusion and gives the Kan property of T after filling the image horn in L. The statement of lem-weil-pbc-trivial-kan-homotopy-equivalence gives a section and the required simplicial homotopy, not merely an assertion about homotopy groups. These two nodes are generic tool uses from other units and are declared in split_report.tool_uses. Thus a=j^L r_1 really is invertible. The same proof works over B without any hypothesis on the functor p.

Step 4 uses the internal-functor/product definitions of def-cbc-enhanced-diagrams-cones and the actual degree-n formula for V in lem-coef-infinity-mapping-composition. I verified monotonicity of q and its equation with every alpha, on each of its three rows. The entire final face is constant, not just its vertices, so the third vertex factor really is constant at z in every degree. These are elementary coordinate calculations, not an implicit invocation of a prism lemma.

Step 5 uses the left-pinch formula in lem-coef-infinity-left-pinch-comparison and the edge-order convention (12,01) in lem-coef-infinity-mapping-composition. I checked both reindexings to 0,i+1. The 01 restriction is exactly the constant simplex at s, including its parameter degeneracies. The witness therefore lies in the fixed-s fiber, as required by the source proof.

Step 6 uses the homotopy equivalence theta, the formula [ell][theta]^{-1} for composition on U and the characterization of precomposition as restriction to an edge vertex, all stated in lem-coef-infinity-mapping-composition. Substitution of Step 5's two strict identities is ordinary algebra in homotopy classes. Step 3 supplies the invertibility needed to turn that identity into the roof description. Precomposing any displayed homotopy with e times the identity explicitly justifies passage to classes on T. I checked that the homotopy equivalence of theta is used as stated, without assuming it is a chosen strictly natural inverse.

Step 7 uses only the internal functor conventions in def-cbc-enhanced-diagrams-cones and the left-pinch formula already read in lem-coef-infinity-left-pinch-comparison. Associativity of composition of simplicial maps proves p(tQ)=(pt)Q; the same computation handles each face and pinch. The fixed s boundary maps to the fixed p(s) boundary, so this proves naturality of the witnesses and their boundaries, beyond just commutation of edge classes. The strict diagram of roofs presents the square with its commutation data; no unsupported assertion about an arbitrary chosen representative of the composition class is made.

I checked delivery-errors B–E against these files. The statement remains self-contained through its named definitions, all non-elementary facts above are actual statements of cited existing nodes, and citations.json copies their statements verbatim. There is no new statement to test or duplicate to justify, no clause moved into a new lemma, no source tag cited as a substitute for a DAG dependency, and no dependency on the parent or any other node depending on this item. Small-case tests were the nerve of an ordinary category (T is the discrete set of choices of g:y-to-z, r_1 is the identity on those choices and the other edge is gs), a degenerate s=id (the same formulas specialize without division), and empty Hom(y,z) (T is empty and the roof leg remains an equivalence). Dimension-zero lifting and degeneracies were explicitly checked. All seven proof steps are below 2000 characters. No SGA source, Lean write or compiler command was used.
