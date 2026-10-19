# Stage-1 report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-bousfield-kan-comparison-calculus.json`: split; six proof steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-simplex-category-last-vertex.json`: one new statement-only node, unsplit; no Mathlib match.
- `citations.json`: one exact statement quotation for every node used in every proof step.

## Attachments

None. Searches by the blueprint tag and by Bousfield–Kan, simplicial replacement, and simplex-category terminology found no finished declaration under the project Lean sources. No Lean was written or compiled.

## WANTED

WANTED: Low, *Revisiting function complexes and simplicial localisation*, arXiv:1409.8062, Definition 1.1, Remark 1.2, Lemmas 1.3–1.4, pp. 3–5; read online at https://arxiv.org/pdf/1409.8062, absent from local literature.

WANTED: Kerodon, https://kerodon.net/tag/01N8, Construction 11.9.11.2 and Corollary 11.9.11.5 (retired subsection replaced by Section 6.3.6); read online for the category-of-simplices last-vertex map. No Stacks tag states this result.

## Errors and corrections

The imported item was unsplit. Its statement agrees with Low and remains unchanged. In particular the BK and KB conventions use opposite chain orders, and must not be conflated. I discarded my initial proposed general simplicial-model-category replacement node: it had no well-defined general diagonal and would have moved the item's content into a new theorem. The final node instead states the independent category-of-simplices last-vertex theorem. The final item proves both invariance and comparison using concrete bisimplicial sets.

## Not duplicates

`lem-coef-simplex-category-last-vertex` vs `lem-coef-bisimplicial-diagonal-equivalence`: the former asserts a particular natural weak equivalence from a category-of-simplices nerve; the latter only asserts preservation of degreewise weak equivalences by diagonal. Neither states the other.

`lem-coef-simplex-category-last-vertex` vs `def-cbc-enhanced-diagrams-cones`: the latter defines nerves, spaces and realization, but gives no last-vertex theorem.

The full DAG and blueprint searches for category of simplices, last vertex, Bousfield–Kan and simplicial replacements found no duplicate. In particular the Thomason node depends on the item, so it was not used to prove it.

`lem-coef-simplex-category-last-vertex` vs `def-sc-invertible-section-ring`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-ample-proj-canonical-map-chart-formula`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-ample-proj-canonical-map-preimage-forward`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-ample-proj-canonical-map-preimage-reverse`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-ample-proj-canonical-map-preimage`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-ample-proj-compatible-quotient-charts`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-proj-chart-pullback-fraction-relation`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-chart-cross-multiplication`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-chart-denominator-generator`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-coefficient-data-arithmetic`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-coefficient-data-numerator`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-coefficient-data`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-coefficient-hom`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-quotient-chart-overlap-base-map-pointwise`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-quotient-chart-overlap-base-map`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-quotient-chart-overlap-sheaf-map`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-quotient-chart-overlap`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-quotient-chart-transfer`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-second-chart-generator`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-sc-section-ring-single-quotient-chart`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

`lem-coef-simplex-category-last-vertex` vs `lem-weil-pbc-sections-morphism-to-proj-polynomial-ring`: the existing statement concerns schemes, section rings or morphisms to Proj; the new statement concerns the weak equivalence from the nerve of a simplex category. The source tags belong to different namespaces (Kerodon 01N8 versus Stacks 01N8).

## Review by Q18

I read Low Definition 1.1 and its displayed BK and KB faces, Remark 1.2 on reversal, Lemma 1.3 on invariance and Lemma 1.4 on diagonal comparison. The final proof follows the same two constructions but supplies an agent-written alternative proof using the category-of-simplices vertex theorem. For the new node I read Kerodon's explicit construction and weak-equivalence corollary. Its arrows use all monotone maps, including degeneracies; it is not the partially ordered set of simplex images. Mathlib's Simplices.lean explicitly distinguishes these notions. I read that file and the truncated homotopy-category file to exclude the search hits as matches. The inherited six new-node searches are present in this item's search log. I reran them for this review, including the second semantic phrasing and both quoted Loogle queries; their hits still do not state the theorem. Searches yielding no declaration are not claimed as matches; failed natural-language Loogle parsing in earlier item searches is not used as evidence for the new node.

For step 1 I checked that the chain-direction simplicial operators and the element-direction operators commute, including endpoint deletion and identities. This is elementary functoriality, and contains no homotopy theorem. Step 2 uses the exact realization definition of weak equivalence in `lem-coef-kan-quillen-right-proper`: realization of the rowwise disjoint union has no relation between chain summands, so components and based homotopies are computed in a single summand. The argument covers an empty chain set. Step 3 takes precisely rowwise-to-diagonal invariance from `lem-coef-bisimplicial-diagonal-equivalence`, whose statement I opened.

In step 4, for each fixed second degree, the KB column is the nerve of the full category of simplices of the first-variable simplicial set. The chain and final-simplex data determine all the other simplices. I checked the maximum-vertex formula against Kerodon's construction and verified that its naturality supplies the second simplicial direction. Step 5 identifies the BK column with the opposite category's nerve and derives its first-vertex map by order reversal from the same new theorem. Reflection of barycentric coordinates gives inverse natural homeomorphisms of realizations, so this does not assume an uncited invariance theorem. The formula sends vertex i to the composite of the first i index maps applied to 0, which is increasing. Step 6 takes the exchanged-direction clause of the diagonal theorem, and checks degree zero explicitly: at index [0] both vertex maps are identities. The comparisons are natural since their chain maps and vertex formulas commute with every simplicial map.

I tested the constructions on the empty simplicial set, a discrete simplicial set, the terminal simplicial set, and a standard 1-simplex. The simplex category is empty in the first case; discrete components stay separate; at a point the category is Delta; and on a 1-simplex the first/last vertex formulas have their required opposite chain orientations. No fibrancy, finiteness, properness, or nonemptiness hypothesis was introduced. Each node citation is quoted verbatim in citations.json. I restored the new node's explicit master and slopmaster2 audit records (both none); the delivery packager owns their treatment in the delivery tree. The new node has no proof steps or proof dependencies; it introduces its simplex category and nerve explicitly, and cites both primitive simplicial sets and the weak-equivalence notion. Its blueprint ancestry includes this item followed by the existing chain to the coefficient adjunction. No unit or chapter route changes. For D1/D2, the new lemma is an independent one-variable subdivision result: it does not mention arbitrary diagrams, preservation of objectwise equivalences, or a bisimplicial diagonal. Steps 4 and 5 identify the replacement columns and explicitly construct the different vertex maps; step 6 still needs the independent diagonal theorem. The item's content is therefore not merely relabelled as a new node.

## Unfinished work

The new last-vertex node remains unsplit, as required for a one-level split. Its later worker can use the cited source's proof. Global check_dag on the shared base reports unrelated pre-existing missing dependencies and cycles; this delivery's required preflight performs the relative check in its temporary worktree.

## Second reading by Q18

- Step 1: checked Low, Definition 1.1 and Remark 1.2 (pp. 3–4), against the displayed BK/KB face and degeneracy formulas; verdict: the two directions, endpoint actions, functoriality, and bisimplicial separation are correct and elementary.
- Step 2: checked Low Lemma 1.3 and the definition of weak homotopy equivalence in `lem-coef-kan-quillen-right-proper`; verdict: realization of the fixed-chain coproduct is a topological coproduct, so the component and based homotopy-group argument covers empty chain sets and is valid.
- Step 3: checked `lem-coef-bisimplicial-diagonal-equivalence` statement verbatim; verdict: its rowwise and exchanged-direction hypotheses give exactly both objectwise invariance conclusions, with no extra finiteness or fibrancy assumption.
- Step 4: checked Kerodon 11.9.11.2 and 11.9.11.5 against the category-of-simplices indexing; verdict: the `T` column is the full simplex-category nerve, the last-vertex formula has the stated monotonicity, and naturality in the second direction is sufficient.
- Step 5: checked Low’s dual BK convention and Kerodon’s last-vertex map after order reversal; verdict: the `B` column is the opposite simplex-category nerve, the first-vertex formula has the correct orientation, and the reversal homeomorphisms justify preservation of weak equivalences and naturality.
- Step 6: checked Low Lemma 1.4 and the exchanged-direction clause of `lem-coef-bisimplicial-diagonal-equivalence`; verdict: the columnwise maps assemble to the two required diagonal comparisons, and the `[0]` summand is the identity as stated.
- New node `lem-coef-simplex-category-last-vertex`: checked its self-contained category, nerve, vertex formula, weak-equivalence notion, Kerodon source, definition dependencies, blueprint ancestry, and recorded searches; verdict: independent strict sublemma, statement-only and not a duplicate, with no Mathlib match.

Changes made: none to the item or node statements, proof steps, citations, or searches. I added this second-reading section only; the existing worker review and all node metadata remain intact. I also tested the empty simplicial set, a discrete simplicial set, the terminal simplicial set, a standard 1-simplex, the zero-index (`r=0`) case, and the `[0]` degree-zero normalization. No SGA source, Lean file, compiler, or shared project file was used.
