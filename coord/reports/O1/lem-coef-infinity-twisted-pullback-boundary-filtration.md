# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-twisted-pullback-boundary-filtration.json`: split the item into five complete finite-set proof steps; statement unchanged; zero new nodes and zero Mathlib leaves.
- `citations.json`: one verbatim citation for the horn-definition dependency used in step 4.
- `report.md`: source, DAG, search, and review audit.

No Lean file was written and no compiler, Lake, or build tool was run.

## Attachments

None. I searched the exact blueprint tag and item id, the key phrases in `WeilConjectures/`, and the upstream reference checkout. No project declaration states this item, and no declaration with this exact statement exists to attach.

## WANTED:

WANTED: an archival copy of Kerodon Proposition 8.1.2.1 (tag 03JW), for `lem-coef-infinity-twisted-pullback-boundary-filtration`. The online page was read directly; the proof origin is therefore recorded as agent-written.

## Corrections and outstanding work

The imported statement agrees with Kerodon 03JW: the finite vertex set, basic subsets, priority, prioritized ordering, horn intersection, and final full face all have the same hypotheses and conclusions. The item had no Lean declaration and no existing proof. I did not create an auxiliary node: the deletion criterion is the proof of this item itself, and moving it to a new node would restate a clause of the item.

I searched the whole DAG and current main-20261015 blueprint for duplicates; the only relevant downstream use is `lem-coef-infinity-twisted-pullback-identity-initial`, which cites this item and does not state the same combinatorial result. Mathlib searches were run with LeanSearch, LeanFinder, Loogle, and grep, each with a second phrasing where applicable. Results were standard simplex/face/horn declarations (`SSet.horn`, `SSet.horn_eq_iSup`, `SSet.face_le_horn`, `SSet.stdSimplex.face_inter_face`) but none states this priority-specific filtration, so the item remains non-Mathlib.

## Review by N1

I read the item node, `dag/units/sk-prop-sf-biduality-general.json`, `dag/chapters/sec-six-functors.json`, and the defining statement of `def-cbc-enhanced-diagrams-cones`. I also read Kerodon tag 03JW, especially the basic-subset setup, the ordered filtration, and the proof of the deletion criterion in lines 31--75.

Step 1 checks that the finite powerset admits the stated ordering and fixes the notation $i=\operatorname{pr}(S_q)=j_k$. It uses only the item’s definitions. Step 2 checks the exceptional deletion $S_q\setminus\{i\}$: it is nonbasic, has priority $i$ but no longer contains its priority, and cannot lie in an earlier prioritized face because priority and then cardinality would force equality. Step 3 checks every deletion $S_q\setminus\{j\}$ with $j\ne i$, including the basic case and both priority comparisons; the resulting prioritized face is strictly earlier. Step 4 converts the codimension-one deletion result into the full intersection equality, using exactly the cited definition’s sentence that a horn is the union of all faces other than the omitted face. Step 5 verifies that $V_n$ itself is the final prioritized subset and therefore its face makes the final union the whole simplex.

I tested the combinatorial criterion by exhaustive enumeration for $n=1,2,3,4,5$; the numbers of prioritized subsets were respectively $4,13,40,121,364$, and every attaching intersection matched $\Lambda_k^d$ for the prescribed priority vertex, independently of tie order. I checked the edge cases where $k=0$, $k=d$, and $n=1$; the item’s combinatorial statement has no exception. No hypotheses were added or dropped, no definition was changed, and no SGA source was used.

The recorded `proof_deps` is exactly the union of step uses. The citation quote is copied verbatim from the current definition node. This sandbox is ready for the second worker’s independent reading and delivery dry run.

## Not duplicates

No new nodes were created. `lem-coef-infinity-twisted-pullback-boundary-filtration` is not a duplicate of `lem-coef-infinity-twisted-pullback-identity-initial`: the latter uses the former’s explicit priority filtration to extend twisted-arrow maps, while this item states only the finite combinatorial filtration and horn-intersection identity.

## Second reading by N1

- Source and item statement: I read Kerodon Proposition 8.1.2.1 (tag 03JW), lines 31–53 and 65–75, against the item statement; the finite vertex set, basic/nonbasic criterion, priority maximum, prioritized ordering, horn index, and final full face agree hypothesis by hypothesis. The statement is unchanged.
- Step 1: checked against 03JW lines 31–55; finiteness and the priority/index notation are elementary consequences of the displayed definitions.
- Step 2: checked against 03JW lines 65–73; the deleted-priority face is nonbasic, has priority $i$ without containing $i$, and the earlier-face contradiction uses exactly the priority then cardinality ordering.
- Step 3: checked against 03JW lines 70 and 74–75; for every other deleted vertex, the basic case is in $K_0$, while the two priority comparisons produce an earlier prioritized face with the required containment.
- Step 4: checked against 03JW lines 54–57 and 65–75 and the cited `def-cbc-enhanced-diagrams-cones` statement; the codimension-one deletion characterization gives precisely the union of all faces except the omitted face, hence the stated horn.
- Step 5: checked against 03JW lines 46–53; $V_n$ is prioritized with priority $n$ and is the unique largest-cardinality subset, so it is $S_m$ and yields $K_m=\Delta^{2n+1}$.
- New nodes: none were created; therefore B1–B7 and duplicate-node checks are vacuous. The existing horn-definition dependency was read at `dag/nodes/sec-smooth-purity/def-cbc-enhanced-diagrams-cones.json`, and the citation quote is verbatim from its statement.
- Edge cases and route: exhaustive finite checks for $n=1,2,3,4,5$ agree with every attaching horn (including $k=0$, $k=d$, and arbitrary tie orders); no hypothesis or conclusion changes and no SGA source is used. The recorded Mathlib searches return only generic horn/face declarations, not this priority-specific filtration.

Changes made during second reading:

1. No mathematical or statement repair was needed after the source comparison.
2. I initially inspected the creation metadata, confirmed that its `created.item` correctly records the original parent split (`lem-coef-infinity-twisted-pullback-identity-initial`) and therefore restored it unchanged; this protected metadata is not the delivered item identity.
