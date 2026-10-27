# Repair of lem-a1-ind-quasi-affine-permanence (Q49)

## Files written

- Item: dag/nodes/sec-purity-real-sheaves/lem-a1-ind-quasi-affine-permanence.json; statement unchanged, three assembly steps.
- dag/nodes/sec-purity-real-sheaves/lem-a1-qc-open-quasi-affine-chart-descent.json: statement, unsplit; no exact or one-line Mathlib match.
- dag/nodes/sec-purity-real-sheaves/lem-a1-qc-open-pullback-quasi-affine-enlargement.json: statement, unsplit; no exact or one-line Mathlib match.
- dag/nodes/sec-purity-real-sheaves/lem-a1-separated-affine-pair-neighbourhoods.json: statement, unsplit; no exact or one-line Mathlib match.

## Attachments

None. The project search in lean/WeilConjectures for the item tag and ind-quasi-affine vocabulary found no completed matching declaration. The existing Sheaf.AlgebraicGeometry.IndQuasiAffinePermanence theorem indQuasiAffineProperty_permanence ends in sorry; it is not an attachment. Its predicate and all three clauses agree with the DAG statement.

## WANTED

None; the cited Stacks TeX sources are present and were read.

## Return repaired

The return requests spreading the 5617-character proof into at least two independent unsplit tasks. This delivery supplies three comparable arguments: old Steps 1-2 (1779 characters), old Steps 3-4 (1821 characters, with affine-cover reduction in the parent), and old Steps 5-7 (2017 characters, with the union-of-two-affines application in the parent). The new item assembly has 1885 characters. Each new node has its own objects and hypotheses, a statement only, no proof or proof dependencies, and logged semantic, Loogle and source searches. Nothing in the original proof has been discarded: the exact seven texts and their original citation lists are below, allocated to the new tasks. The source and route, rather than an alternate argument, determine the allocation.

The sandbox initially contained only dispatcher markers; there was no previous node, report, citations or searches to reuse. I took the complete current repository node as the returned proof and preserved every unrelated field, including Lean records, old searches and review records. The delivery tool rebases the owned split fields onto the server head. The current node statement is unchanged; no statement dispute was found.

## New nodes

1. lem-a1-qc-open-quasi-affine-chart-descent treats a fixed compact open over an arbitrary qcqs target open, under absolute quasi-affineness on the affine charts. This extends the actual chart-refinement argument of 0F1U (3) => (4). The task includes the affine-source/morphism translations used in old Step 1 and the compactness/refinement argument of old Step 2. It does not state P, its locality equivalence or the other permanence clauses.
2. lem-a1-qc-open-pullback-quasi-affine-enlargement constructs the finite affine enlargement W, gives the induced open immersion into W times_A B, and asserts quasi-affineness of that ambient pullback and L. This isolates the geometric work in old Steps 3-4; reduction from general base changes to affine charts remains in the parent. It does not assert arbitrary base-change stability of P. Its proof source is the explicit agent expansion of 0AP7 already accepted in the returned split, using the finite affine enlargement from the neighbouring composition proof and ordinary 01SO.
3. lem-a1-separated-affine-pair-neighbourhoods assumes pairwise separated neighbourhoods, without any quasi-affine assumption, and gives the absolute closed diagonal and quasi-separatedness. Its work is the diagonal cover and direct closed-immersion verification from old Steps 6-7. Old Step 5 supplies the neighbourhoods in the parent. Thus it is not a restatement of clause (3), and applies to schemes beyond ind-quasi-affine schemes.

## Review by Q49

I read Stacks more-morphisms.tex at definition-ind-quasi-affine (0AP6), its following separatedness paragraph, lemma-ind-quasi-affine-alternative-definition (0F1U), the neighbouring composition argument and lemma-base-change-ind-quasi-affine (0AP7). For chart descent I checked the qcqs target hypothesis in the source: it makes K -> V quasi-compact, so inverse images of affine refinement opens are compact. The affine refinements lie inside some U_i; neither V intersect U_i nor the target is silently assumed separated. Morphisms 01SM, lemma-characterize-quasi-affine, supplies precisely the affine-cover criterion. I also read Morphisms 01SO and Properties 01P9 for the enlargement and separated-neighbourhood application. The proof_origin stays agent: the old split replaces the composition shorthand of 0AP7 by a fully specified enlargement argument, and the separatedness paragraph is expanded to a diagonal cover.

Assembly Step 1 uses exactly the equivalence in lem-a1-quasi-affine-target-locality on a singleton affine cover, the conclusion of the new chart-descent node, and affine qcqs from lem-weil-pbc-affine-scheme-qcqs. Every hypothesis of chart descent is supplied by P on the given U_i. The reverse implication only regards affine opens of an open subscheme as affine opens of Y; it invokes no descent theorem.

Assembly Step 2 uses the full neighbourhood-basis assertion of lem-weil-pbc-affine-opens-basis to obtain affine V_b inside g inverse U_i, not an assertion that arbitrary intersections of affine opens are affine. It uses the finite-enlargement node with A=U_i, B=V_b, X=f inverse U_i and with the already obtained absolute quasi-affineness of every compact open of that X. The base changes identify by the universal property of def-pc-fibre-product. In particular, the argument is applied to an arbitrary compact open over each affine V' inside V_b; it does not stop at the whole V_b, which was the earlier reviewer's correction. The singleton criterion converts its absolute quasi-affineness to L -> V'. The proved Step 1 glues P.

Assembly Step 3 uses the singleton criterion for the whole affine Y. Affine compactness in lem-weil-pbc-affine-scheme-qcqs gives compactness of A and B; the finite union argument is written explicitly. The statement of lem-trf-quasi-affine-canonical-affine-embedding actually includes separatedness, which is the only part taken here. The new pair-neighbourhood criterion then gives the closed absolute diagonal and quasi-separatedness, as its statement says. I opened every node in these three uses lists; citations.json copies their statements verbatim.

For each new task I compared the source and statement, checked every object was introduced and each non-inline notion had a definition dependency. I searched the whole DAG by source tags and by the statement vocabulary, the whole blueprint via blueprint_refs.py (ind-quasi-affine, quasi-affine, separated open, 0AP7, quasi-compact open and separated/affine terms), and the project Lean. The ordinary target-locality node, ordinary base-change node and the canonical embedding leaf were reused rather than duplicated. The logged Mathlib searches include two semantic phrasings per task, LeanSearch, Loogle and source grep. I read their hits and inspected QuasiAffine.lean and Separated.lean: the generic HasAffineProperty lemmas assume locality instead of proving the new chart property, the pullback compactness lemmas do not provide the chosen finite enlargement and quasi-affineness, and the separatedness instances do not establish a pairwise-neighbourhood criterion. Hence all three new nodes remain unsplit, with no unrun search claimed.

Edge cases: empty schemes and empty L use n=0 and the empty open; the empty scheme is affine/quasi-affine. A singleton affine cover reduces chart descent to ordinary quasi-affineness and the compact-open condition. For an infinite affine cover only a finite cover of the projected compact subset is chosen, not of X or Y. Neither projection is assumed injective, affine on X, or to carry affine opens to affine opens. The doubled-origin line fails the pair-neighbourhood hypothesis for its two standard affine charts, as required. The pair criterion needs no compactness on W; it covers X times_S X by the opens W times_S W chosen for the two projections. Restricting the diagonal over those opens gives Delta_W, and local sheaf surjectivity is checked on that target cover.

I checked delivery-errors B-E point by point. New nodes have no proof sketches in their statements and no proof steps, complete TeX, correct source labels and blueprint ancestry; all declarations searched are recorded faithfully. There is no cycle back to the item. The new statements are different geometric intermediate arguments rather than copies of its clauses. No node uses the proof of another node in place of its statement. Each parent step is below 2000 characters and the full assembly is below 3000. All extracted arguments remain verbatim below for the future workers; shortening the parent has not removed them. No Lean, compilation, library edits, launcher edits, SGA source or extra agent was used.

## Not duplicates

- lem-a1-qc-open-quasi-affine-chart-descent vs lem-a1-ind-quasi-affine-permanence: The existing item proves three permanence clauses for P; this node isolates the qcqs-target compact-open affine-chart descent argument with absolute chart hypotheses.
- lem-a1-qc-open-pullback-quasi-affine-enlargement vs lem-a1-ind-quasi-affine-permanence: The existing item proves three permanence clauses for P; this node isolates finite affine enlargement and the induced open embedding after an affine-base pullback.
- lem-a1-qc-open-pullback-quasi-affine-enlargement vs lem-trf-quasi-affine-base-change: This node concerns a finite affine enlargement inside a pullback; the existing node instead states Quasi-affine morphisms are stable under arbitrary base change.
- lem-a1-separated-affine-pair-neighbourhoods vs lem-a1-ind-quasi-affine-permanence: The existing item proves three permanence clauses for P; this node isolates the absolute diagonal criterion with pairwise separated-neighbourhood hypotheses.

- lem-a1-qc-open-quasi-affine-chart-descent vs lem-a1-quasi-affine-target-locality: ordinary locality assumes the actual preimages of a target cover are quasi-affine; the new node must first refine target charts and prove these restricted compact opens are quasi-affine. The hypothesis concerns all compact opens of f inverse U_i, not only the preimages for a single morphism K -> V.
- lem-a1-qc-open-pullback-quasi-affine-enlargement vs lem-trf-quasi-affine-base-change: ordinary base change begins with a quasi-affine morphism; the new statement allows arbitrary X -> A and constructs a compact W that encloses the projected L before that theorem applies.
- lem-a1-separated-affine-pair-neighbourhoods vs lem-trf-quasi-affine-canonical-affine-embedding: the latter starts with a single quasi-affine scheme; the new criterion concerns a possibly noncompact X with different separated opens for different pairs.

## Original proof retained and allocation of all work

These are the returned node's complete step texts verbatim, not new proof fields on the unsplit tasks. They give each future worker the entire original argument. Their citation files can be read in the repository; the parent now cites the extracted statement nodes instead.

### Original Step 1 -> lem-a1-qc-open-quasi-affine-chart-descent

First record two elementary translations. If $q:Q\to A$ has affine target and is quasi-affine, then $Q$ is quasi-affine by applying [def-nagata-quasi-affine-morphism] to the whole affine open $A$. A quasi-compact open $L$ of a quasi-affine scheme $Q$ is again quasi-affine: compose its open inclusion with an open embedding of $Q$ into an affine scheme; the image of $L$ is open and quasi-compact. Conversely, if $Q$ is quasi-affine and $A$ affine, [lem-weil-pbc-affine-scheme-qcqs] and clause (1) of [lem-weil-pbc-qcqs-morphism-permanence] make any $q:Q\to A$ quasi-compact. The inverse image of every affine open of $A$ is thus a quasi-compact open of $Q$, hence quasi-affine by the preceding argument, which is precisely the definition that $q$ is quasi-affine.

Original uses: def-nagata-quasi-affine-morphism, def-weil-open-immersion, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence.

### Original Step 2 -> lem-a1-qc-open-quasi-affine-chart-descent

For clause (2), the forward implication is immediate: an affine open of $U_i$ is also an affine open of $Y$, and the corresponding inverse-image open and induced map are unchanged. For the converse, assume $P$ for each restriction to $U_i$. Fix an affine open $V\subseteq Y$ and a quasi-compact open $K\subseteq f^{-1}(V)$. The map $q:K\to V$ is quasi-compact by [lem-weil-pbc-affine-scheme-qcqs] and [lem-weil-pbc-qcqs-morphism-permanence](1). Use [lem-weil-pbc-affine-opens-basis] to cover $V$ by affine opens $V_a$, each contained in some $U_{i(a)}$. Since $q$ is quasi-compact, $K_a=q^{-1}(V_a)$ is quasi-compact. It is open in $f^{-1}(U_{i(a)})$, so the hypothesis $P(f|_{U_{i(a)}})$ applied to the whole affine target $U_{i(a)}$ gives a quasi-affine map $K_a\to U_{i(a)}$. Step 1 makes $K_a$ a quasi-affine scheme. Apply [lem-a1-quasi-affine-target-locality] to $q$ and the affine cover $(V_a)$: $K\to V$ is quasi-affine. This proves $P(f)$. In particular, no intersection $V\cap U_i$ has been assumed affine.

Original uses: lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-affine-opens-basis, lem-a1-quasi-affine-target-locality.

### Original Step 3 -> lem-a1-qc-open-pullback-quasi-affine-enlargement

For clause (1), let $g:T\to Y$ be arbitrary and put $X_T=X\times_YT$. Choose an affine open cover $(U_i)$ of $Y$. By [lem-weil-pbc-affine-opens-basis], $T$ has an affine open cover $(V_b)$ with each $V_b\subseteq g^{-1}(U_{i(b)})$. Clause (2), already proved, reduces the assertion to $X\times_YV_b\to V_b$ for each $b$. Fix $b$ and a quasi-compact open $L\subseteq X\times_YV_b$. Its image under the first projection is a quasi-compact subset of $f^{-1}(U_{i(b)})$: pull any open covering of that image back to $L$ and take a finite subcover. Cover that image by affine opens contained in $f^{-1}(U_{i(b)})$, using the affine-open basis again, and retain finitely many. Their union is a quasi-compact open $W\subseteq f^{-1}(U_{i(b)})$ containing the image. The projection $L\to X$ factors through $W$, since a morphism whose image lies in an open subscheme restricts to it [def-weil-open-immersion].

Original uses: lem-weil-pbc-affine-opens-basis, def-pc-fibre-product, def-weil-open-immersion.

### Original Step 4 -> lem-a1-qc-open-pullback-quasi-affine-enlargement

The hypothesis $P(f)$ makes $W\to U_{i(b)}$ quasi-affine. By [lem-trf-quasi-affine-base-change], its base change $W\times_{U_{i(b)}}V_b\to V_b$ is quasi-affine. Since $V_b$ is affine, its source is quasi-affine by Step 1. The inclusion of $W\times_{U_{i(b)}}V_b$ into $X\times_YV_b$ is an open immersion by [lem-weil-pbc-open-immersion-base-change]. Its image contains $L$, by construction of $W$, so $L$ is a quasi-compact open of that quasi-affine source. Step 1 makes $L$ quasi-affine. Now let $V'\subseteq V_b$ be any affine open and $L$ any quasi-compact open of the inverse image of $V'$; the argument above applies verbatim to $L$ (only $L\subseteq X\times_YV_b$ was used), so $L$ is a quasi-affine scheme, and the converse part of Step 1, with the affine target $V'$, makes $L\to V'$ quasi-affine. Thus $P(X\times_YV_b\to V_b)$ holds for every $b$; the reduction in Step 3 proves arbitrary base-change stability.

Original uses: lem-trf-quasi-affine-base-change, lem-weil-pbc-open-immersion-base-change.

### Original Step 5 -> lem-a1-separated-affine-pair-neighbourhoods

For clause (3), suppose $Y$ is affine. Apply $P(f)$ to $U=Y$: every quasi-compact open $K\subseteq X$ has quasi-affine map $K\to Y$, so Step 1 makes $K$ a quasi-affine scheme. In particular, for any two affine opens $A,B\subseteq X$, their union $W=A\cup B$ is quasi-compact: an open cover has finite subcovers on $A$ and on $B$. Hence $W$ is quasi-affine. By [lem-trf-quasi-affine-canonical-affine-embedding], $W$ is separated, so its absolute diagonal is a closed immersion.

Original uses: lem-weil-pbc-affine-scheme-qcqs, lem-trf-quasi-affine-canonical-affine-embedding, def-weil-proper-morphism.

### Original Step 6 -> lem-a1-separated-affine-pair-neighbourhoods

Write $S=\operatorname{Spec}\mathbf Z$ and $D=X\times_SX$. For every pair of affine opens $A,B$ of $X$, set $W=A\cup B$ as in Step 5. The two projection inverse images of $W$ are open in $D$; their intersection is the open subscheme $D_W=W\times_SW$, by [lem-weil-pbc-open-immersion-base-change] and the fibre-product universal property. These $D_W$ cover $D$: the projections of any point of $D$ belong to some affine opens $A$ and $B$, by [lem-weil-pbc-affine-opens-basis]. The inverse image of $D_W$ under the absolute diagonal is $W$, and the restricted diagonal is exactly $\Delta_W$ (both components are the identity). It is a closed immersion by Step 5.

Original uses: def-pc-fibre-product, lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-affine-opens-basis.

### Original Step 7 -> lem-a1-separated-affine-pair-neighbourhoods

Check the closed-immersion definition [def-weil-closed-immersion] directly for $\Delta_X$ on the cover $(D_W)$. Its image is closed because its intersection with each $D_W$ is the closed image of $\Delta_W$. The diagonal is injective (its composite with the first projection is the identity). Its inverse onto the image is continuous, being the restriction of the first projection, so it is a homeomorphism onto this closed image. Finally, the structure-sheaf map is surjective: a section germ can be lifted locally in any $D_W$ containing the point, since the restricted map is that of the closed immersion $\Delta_W$; these are exactly the local lifts required for surjectivity of a map of sheaves. Thus $\Delta_X$ is a closed immersion and $X$ is separated [def-weil-proper-morphism]. Apply [lem-pc-separated-quasi-separated] to $X\to S$ to conclude that $X$ is quasi-separated.

Original uses: def-weil-closed-immersion, def-weil-proper-morphism, lem-pc-separated-quasi-separated.

## Unfinished work

The proofs of the three new unsplit nodes are intentionally left to separate workers, as required by this return. This delivery completes the stage-1 re-split only. No mathematical obstruction or missing source was found.
