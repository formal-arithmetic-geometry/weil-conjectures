# Stage-1 report: lem-pod-texact-truncation-triangle-comparison

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-texact-truncation-triangle-comparison.json`: statement item, now split into four steps using existing nodes. Its statement and statement dependencies are unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: eight citations, one for every step/node pair, with verbatim quotations from the current statements.
- `report.md`: this report. `searches.jsonl` contains the six real msearch calls made here; the item's inherited Q25 searches were retained. `bbd-28-36.txt` is a sandbox-only PDF extraction for reading, not delivery material.

## Attachments

None. The project declaration `CategoryTheory.Functor.eTruncGEδLT_comm` in `lean/WeilConjectures/Mathlib/CategoryTheory/Triangulated/TStructure/SpectralObject.lean:244` is sorry-free in the source and proves the boundary square using the specified shift comparison. The natural truncation isomorphisms are defined at lines 168 and 186, their normalization equations at lines 135 and 159. These are partial coverage: no single declaration found states the entire item's existence/uniqueness and both triangle-naturality assertions. The generic uniqueness results in `ShortExact.lean` are already attached to `lem-weil-heart-short-exact-triangles`, which this split reuses. No new declaration or duplicate attachment is proposed.

## WANTED

None. BBD is present locally. No SGA reference is used. BBD Proposition 1.3.3(i),(ii), printed pp. 29–30, is the source of abstract truncation adjunctions and uniqueness of the entire triangle including the degree-one arrow. There is no Stacks tag for this abstract t-structure result, as the existing definition and heart nodes explain; complex truncation tags would impose a different ambient category.

## Findings and changes

The imported item was statement-only; there was no earlier sandbox attempt. I read the current main-20261015 operations statement and proof, the chapter record and unit sk-lem-finite. This item serves the operations proof's sentence about commuting with truncations, through the fixed-pair truncation/cohomology node. Its generic argument adds no change to that route or to the unit/chapter statement. There is no blueprint_update on the item and no released repair note for it.

The full triangle uniqueness needed here already appears in clause (1) of `lem-weil-heart-short-exact-triangles`; adding a separate uniqueness lemma would duplicate it. The adjunctions there also give exactly the cancellation needed for components and for naturality of the last arrow. The existing comparison node gives the normalized natural isomorphisms, but does not itself assert the boundary square: Step 2 obtains that square from an actual isomorphism of distinguished triangles. Step 3 writes out the TR3 completion and the identification of its third component, instead of asserting that a boundary map is automatically natural. Step 4 writes out the use of naturality of the shift comparison.

I searched the whole DAG by truncation uniqueness, triangle orthogonality, BBD 1.3.3 and declaration names, and searched the blueprint with `ancestor`, `search truncation`, `search triangle`, `search t-exact`, `search unique isomorphism` and `search truncation triangle`. The generic heart node is reused; no blueprint node states this whole functor-specific item in another form, so same_as remains empty. No new node was needed.

All six new Mathlib searches were made with msearch.py, with two semantic phrasings. Loogle returned no hits for the combined truncation/triangle/functor query. The semantic services returned the definition and preservation property of triangulated functors, exactness for homological functors, spectral-object connecting maps, and generic constructors for triangle isomorphisms. The source searches found `triangleLEGE`, `truncGEδLE`, `eTruncGEδLT` and existing spectral-object constructions. I read the relevant Mathlib Functor, TruncLEGT, ETrunc and SpectralObject infrastructure and the stronger project SpectralObject module. The pinned Mathlib does not contain the arbitrary t-exact-functor normalized triangle comparison with all the item's clauses; the project boundary result alone does not justify marking the item as Mathlib or ATTACH.

## Unfinished work

None at the level of the requested one-level split. The stage-1 proof uses existing nodes only, and does not purport to write or compile a Lean proof. The required deliver.py --no-push completed with exit code 0 and printed OK: server preflight passed (dry-run commit e204d384420). This includes the required server-side DAG and split checks; no compiler was run.

## Not duplicates

No new nodes. In particular no copy of BBD truncation uniqueness, TR3, or the comparison-isomorphism statement was created. The existing heart lemma is strictly more general than the particular uniqueness tool used here, while the comparison lemma supplies the two normalized component isomorphisms and leaves their boundary compatibility to this item.

## Review by Q22

I read BBD Proposition 1.3.3(i),(ii) in the local PDF extraction, printed pp. 29–30. Its proof first derives the truncation adjunction from Hom exactness and orthogonality and then proves uniqueness also for the degree-one arrow. This warrants the whole-triangle uniqueness in the existing heart node, rather than only uniqueness after forgetting the boundary. There are no new nodes requiring separate source verification. I checked the four steps against the statements of every cited node, and copied the portions used to citations.json.

For Step 1, clause (1) of `lem-weil-heart-short-exact-triangles` states the distinguished triangle and its two bounds. `def-weil-triangulated-category` explicitly defines exactness as preservation of distinguished triangles with the shift isomorphism. `def-weil-t-structure` fixes the degree convention. Thus the image's first and third objects have precisely the <= m and >= m+1 bounds required for the next use of uniqueness. This is a direct use of the definitions and hypotheses, marked elementary, not an unproved preservation theorem.

For Step 2, the heart node's clause (1) states uniqueness of the entire truncation triangle over its middle object and both adjunctions; it is not merely a definition of the heart. These hypotheses hold in D by Step 1. The comparison node states both normalization equations and that both comparisons are isomorphisms. The right adjunction identifies the first component. For the third component I deliberately use b(c^+)^{-1} on the canonical target truncation, where left-adjunction injectivity applies: cancellation directly against F(pi) would require justification. The calculation b(c^+)^{-1} pi = b F(pi) = pi supplies that justification. The resulting third square has exactly the chosen s and no extra sign.

For Step 3, the heart node supplies actual truncation functors and adjunctions, hence natural unit and counit. The triangulated-category definition explicitly states TR3 with the final shifted square. After completing the first square, both candidate maps V_K to V_L have the same composite with pi_K. The left adjunction applies since V_L lies in C^{>= m+1}, and identifies the TR3 component with tau^{>= m+1}(v). Its last square is therefore exactly the claimed boundary naturality equation. This uses neither a cone functor nor uniqueness of arbitrary cone morphisms.

For Step 4, naturality of both component comparisons is explicitly in `lem-pod-texact-truncation-comparison`. The displayed calculation of s F(delta_L) F(V(v)) uses the boundary square already proved and naturality of the given coherent shift comparison, not a new compatibility assumption. Naturality of the triples is then equality of their three components; all three components are already isomorphisms by Step 2. This step is elementary assembly from the cited naturality and previous steps.

I tested the statement at K=0, v=0, v=1, and F=identity, where the formulas reduce to identities or zero. For K in C^{<= m}, the upper triangle term is K and the other is zero; for K in C^{>= m+1} the reverse holds. Both adjunction arguments still apply without assuming a truncation arrow is monic or epic. Taking F=0 also leaves all assertions valid. No boundedness strengthening, faithfulness, exactness of an abelian functor, or choice of a different shift comparison was used; boundedness is retained although this proof works without it.

Against delivery-errors B–E: statements and metadata are preserved, sources are precise, genuine searches and their verdicts are recorded, each citation supplies the asserted result, all TR3/adjunction hypotheses have been checked, and there is no cycle or new unsplit proof hidden in a node. The longest step is under 900 characters; no step crosses the 2000-character long-step threshold. Steps 2 and 3 are marked non-elementary and cite the existing non-elementary theorem they use. Steps 1 and 4 are direct definition and naturality calculations. No statement dispute or source correction was needed.
