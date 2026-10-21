# Q90: def-nagata-scheme-image-factor

## Files written

- `dag/nodes/sec-nagata-compactification/def-nagata-scheme-image-factor.json`: existing definition, now a Mathlib leaf. The canonical map is `AlgebraicGeometry.Scheme.Hom.toImage` (Subscheme.lean:710); its factorization equality is `AlgebraicGeometry.Scheme.Hom.toImage_imageι` (Subscheme.lean:715).
- `citations.json`: empty list, since a Mathlib leaf has no proof steps.
- `report.md` and the actual command-generated `searches.jsonl`.

Zero new nodes; one Mathlib leaf (the item).

## Attachments

None. Searches by the blueprint id and by the canonical-factor names in `lean/WeilConjectures/` found no declaration covering this item for an arbitrary scheme morphism. `ChowLemma/Graph.lean` has a specialization for its graph, which does not cover the item's generality. Mathlib declarations are delivered as a leaf, not as a project attachment.

## WANTED

None.

## Corrections and observations

Followed the `blueprint_update` and the current main-20261015 definition at order 76, rather than retaining the older implementation-only wording at order 68. Explicitly introduced the schemes and morphism; the mathematical assertion is unchanged. Retained the historical import flags, blueprint metadata, audit and Lean record. Removed `def-nagata-scheme-theoretic-closure` and `lemma-nagata-scheme-image-ideal-qc` from statement dependencies: this definition uses the image notion alone, and its entire construction/equality is now matched directly to Mathlib. The cited image definition's current statement now agrees with Mathlib's largest quasi-coherent ideal contained in the sheaf kernel, without a quasi-compactness assumption. Its formerly imported largest-closed-subscheme wording has been corrected by its own landed delivery. This repair explicitly adopts its current kernel convention in the item and the Mathlib match; the other node is untouched.

The initial grep omitted `Hom.` and returned no hits. A broad single-file grep showed auxiliary construction lines and the wrapper parsed its line fragments as file fields. Both actual outputs are retained honestly. The refined directory grep supplies the correct declaration names, paths and lines. LeanFinder, Loogle and LeanSearch all found the exact map and factorization theorem; no service was unavailable.

## Unfinished work

None for this stage-1 item. No Lean was written or compiled.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches for `toImage`, `canonical factor` and `scheme-theoretic image` found the existing item and related nodes. The interface node `lemma-nagata-scheme-image-ideal-qc` additionally asserts quasi-compact section/stalk injectivity and support closure; it is not an alternative definition of the canonical map. The universal-property node additionally asserts closed-factorization minimality. No duplicate node was created for either clause.

## Review by Q90

I read `coord/delivery-errors.md` B–E in full, the three levels in SETUP, GOAL, the chapter and unit, the current blueprint definition, and Stacks `morphisms.tex`, Tags 01R6 (`lemma-scheme-theoretic-image`) and 01R7 (`definition-scheme-theoretic-image`). Stacks explicitly supplies a factorization through the smallest closed subscheme for any morphism and explains the largest quasi-coherent subideal when the sheaf kernel is not quasi-coherent. This is consistent with the current blueprint; imposing quasi-compactness here would unnecessarily restrict the definition.

I read Mathlib `IdealSheaf/Subscheme.lean` lines 659–719, including the auxiliary construction and its specification. `Hom.image` at 662 is exactly the subscheme of `g.ker`; `Hom.imageι` at 665 is its subscheme inclusion. `Hom.toImage` at 710 is the actual canonical map, constructed from the glued local quotient maps with a copied underlying point map. `Hom.toImage_imageι` at 715 has exactly the equality needed, in Lean's left-to-right composition order. I separately read `Morphisms/ClosedImmersion.lean` lines 94–95: its instance states `IsClosedImmersion I.subschemeι`, which applies directly to `I = g.ker`. Thus the data, closed inclusion and equality all match; no identification theorem is hidden in the leaf.

There are no proof steps, so C1/C4 impose no step citations and `citations.json` is empty. I opened all three old statement dependencies: the closure definition concerns a special immersion and is not used; the interface lemma supplies additional theorems not needed here; the image definition is the retained notion. The leaf uses no proof of any DAG node and introduces no cycle or off-unit tool use. B1–B9 hold without any new nodes; B10 was checked against project source and the exact finished declarations are in Mathlib. D1–D5 do not arise because no clauses are repackaged as new lemmas. E1–E7 were checked against the unrestricted Mathlib variable context and the source's warning about non-quasi-compact maps.

For small cases, the empty source gives the empty image and its unique factorization; an identity factors through its own image; an affine map A → B factors as A → A/ker → B on rings. Nonreduced examples such as Spec(k) → Spec(k[ε]/(ε²)) use the quotient by (ε), so the construction retains scheme structure rather than merely a topological image. The general non-quasi-compact case remains covered by the quasi-coherent kernel construction and the theorem has no extra assumptions. None of these checks suggests a statement dispute. There are no long proof steps and no added axioms or hollow definitions.

## Repair of the returned delivery

Return point L: the landing refused the previously approved delivery because `def-nagata-scheme-theoretic-image` changed after review. I compared the retained item with the current repository item field by field, and re-read the full current statements of the retained dependency and both removed imported dependencies. The current item is still imported, so this repair is not superseded. The delivery command rebuilds the commit on the current server DAG; no git command was run in the read-only repository.

The changed cited node now says: “Its *kernel ideal* $\ker(g)\subseteq\mathcal O_Y$ is the largest quasi-coherent ideal contained in the kernel of $\mathcal O_Y\to g_*\mathcal O_T$ (this kernel itself when $g$ is quasi-compact).” It then defines SIm(g) as the closed subscheme cut out by that ideal, with its inclusion and factor map. Its status is now `mathlib`, reviewed by L. These are precisely the image object and inclusion this item uses. Neither its density convention nor its closure clause is used here. Its parenthetical ordinary-kernel identification applies only under quasi-compactness and is not used for arbitrary g.

I checked that convention directly in Mathlib: `Hom.ker` at Basic.lean:692–694 is `ofIdeals` of the affine section kernels; `ofIdeals` at :104–105 and `le_ofIdeals_iff` at :125–126 supply the largest compatible ideal. Subscheme.lean:662 and :665 define `Hom.image` and `Hom.imageι` from that very ideal. The context at :659 has arbitrary scheme morphism f, with no quasi-compactness instance. `Hom.toImage` at :710–712 and `Hom.toImage_imageι` at :715–718 therefore still provide exactly this item's data and equation. The closed-immersion instance at ClosedImmersion.lean:94–95 applies to the same ideal. There is no comparison with an independently defined image to prove.

The node now states the largest-quasi-coherent-kernel convention explicitly and its `mathlib_match.how` records the identification with the revalidated dependency and the Basic.lean lines. Its `split_report.summary` documents that revalidation. I corrected the report's stale assertion that the cited node still had the old erroneous statement. The existing Mathlib searches still answer the same question about the same arbitrary factorization map, so I read and retained their command-generated results without repeating them or adding invented searches. The item remains a Mathlib leaf with no proof steps; `citations.json` remains `[]`. The only retained statement dependency is the changed image definition, and its current statement supplies both the image and its closed inclusion. The closure and interface nodes were also re-read: the former specializes images to immersions and the latter adds injectivity and support assertions, none needed for this definition.

Review B–E still holds after repair: no new nodes or duplicate clauses, no non-elementary step hidden in prose, no off-unit proof dependency, and no long proof steps. The empty-source, identity, affine quotient and nonreduced checks above apply to the same kernel construction. For non-quasi-compact g the canonical factorization still exists; this item makes no assertion of open-restriction compatibility, raw-kernel quasi-coherence or topological density. Thus no new hypothesis or conclusion has entered the item.

The required initial dry run of the retained sandbox exited successfully at `6f864f7210d` before these repairs. A new dry run is required for the repaired files before pushing.
