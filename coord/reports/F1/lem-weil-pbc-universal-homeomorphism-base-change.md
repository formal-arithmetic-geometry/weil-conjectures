# Worker report: lem-weil-pbc-universal-homeomorphism-base-change

## Files

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-universal-homeomorphism-base-change.json`: exact Mathlib leaf; no new node.
- The statement now cites the precise notion node `def-weil-universal-homeomorphism` in place of the conventions bundle, without changing its meaning.

## Mathlib match

The project's pinned Mathlib revision is `0df444a360eaa60ab8c11dca51a86af692955474` (slopmaster2 `lake-manifest.json`). In that checkout, `Mathlib/CategoryTheory/MorphismProperty/Limits.lean:872-873` defines `P.universally f` as `P` holding for every pullback of `f`. `Mathlib/AlgebraicGeometry/Morphisms/Constructors.lean:259-262` defines `topologically IsHomeomorph` as the homeomorphism property of the map on underlying spaces. Thus the notion node's definition is exactly `(topologically IsHomeomorph).universally` on schemes. `CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange` at `Limits.lean:889-891` specializes with this `P` and gives the item's conclusion for any base change in one line. Its proof pastes pullback squares, matching the imported blueprint proof and Stacks Morphisms Lemma 0CEU. LeanSearch, Loogle, and source grep results are recorded on the node.

## Attachments

None. The earlier candidate `AlgebraicGeometry.IsUniversalHomeomorphism.instIsStableUnderBaseChangeScheme` is sorry-free, but its class uses integral + universally injective + surjective. Stacks 04DF identifies that class mathematically with the quantified notion; the converse bridge is not formalized in the source, so it is not attached as an exact declaration.

## Blueprint and source

`tools/blueprint_refs.py search universal homeomorphism base change` found this blueprint node plus site-invariance statements, with no second blueprint node stating this same lemma. `blueprint.same_as` is therefore `[]`. The `split_report.blueprint` identifies the sole proof sentence realized by Mathlib's pullback-pasting instance. Stacks source checked in `/tmp/stacks-project/morphisms.tex`: Definition 04DD, Lemma 0CEU, and the characterization Lemma 04DF.

## Problems and unfinished work

The original imported proof was correct mathematics but unnecessary as a split once the exact Mathlib generalization is used. The blueprint source file named by the item is not present in this clone; its statement and proof are preserved in the imported DAG version and agree with the Stacks source. No proof obligation remains in this item.

## Review by F1

I read Stacks `morphisms.tex`, Definition `definition-universal-homeomorphism` and Lemma `lemma-base-change-universal-homeomorphism` (lines 11304-11321). The item has exactly that statement: any pullback of a morphism whose every pullback is a homeomorphism again has the same property. I checked the cited `def-weil-universal-homeomorphism` node: it quantifies over all scheme base changes, with no integral/surjective reformulation hidden in the statement.

I checked pinned Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` directly: `Limits.lean:872-873` defines `P.universally` by all pullback squares, `Limits.lean:889-891` supplies stability under base change, and `Constructors.lean:259-262` turns the underlying-map `IsHomeomorph` property into a scheme morphism property. The specialization is one line at the level of these definitions; no theorem about the distinct slopmaster2 integral/injective/surjective class is assumed. This addresses B6/B8 and E1/E6, including the identity and iterated-pullback cases. The Mathlib leaf has no proof steps or new nodes, so B1-B5/B7, C1-C8 and D1-D5 add no obligations; `same_as=[]` is consistent with the blueprint search recorded by the worker.

I sent the first attachment proposal back because slopmaster2's `IsUniversalHomeomorphism` class uses the Stacks 04DF characterization, while the node uses the quantified 04DD definition; the source checkout does not formalize the converse bridge. The worker replaced it with the exact general Mathlib leaf. No further correction is needed. I checked the item diff and report for A1-A7 and the source-based checks of F1-F5 before packaging.
