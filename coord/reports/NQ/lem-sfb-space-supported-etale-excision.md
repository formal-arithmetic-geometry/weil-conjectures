# Stage-1 delivery: lem-sfb-space-supported-etale-excision

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-supported-etale-excision.json`: statement, split into eight proof steps; not a Mathlib leaf. The statement, its statement dependencies and the imported provenance are retained.
- No new DAG nodes; zero new Mathlib leaves.
- `citations.json`: 21 verbatim statement quotations, one for each step/node citation.
- `searches.jsonl`: actual search-command records; the item retains its previous searches and adds these results.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, supported/etale/excision terminology, algebraic spaces and elementary distinguished squares. The nearby `SupportsEtale.lean` statements are about schemes with constant coefficient rings, not the unbounded structure-sheaf module assertion on algebraic spaces here. They cannot attach this item.

## WANTED

None. The needed Stacks sources are present.

## Corrections and scope

The item was unsplit, with no prior sandbox item or report and no repair note. Its mathematical statement is correct and is unchanged. I replaced the empty proof with an argument using existing nodes. There is no STATEMENT-DISPUTED issue.

I read the current blueprint through `literature/blueprint/latest/`, in particular the direct-images proof (3), and the chapter/unit records. The inherited provenance traces this foundational input through the supported Koszul localization argument to that direct-image step. I changed neither the unit nor its route. This item is not its unit's key statement, so no unit realization record was written. The ancestor command currently returns None for the inherited chain; I retained its existing null `from.node`, precise `from.place` and `via` list rather than inventing an ancestry change.

The proof follows the same support, exact sum-extension and derived-adjunction ingredients as Stacks 08GG, but proves the supported right-unit assertion using the already existing unbounded Hom Mayer–Vietoris node (08H9). It is therefore honestly marked `proof_origin.by = agent`; it is not represented as a transcription of the printed section-reduction proof. This avoids creating clause-shaped nodes for the conclusion of 08GG.

## Not duplicates

There are no new nodes and therefore no new/existing pairs requiring justification. I searched the entire DAG for 08GG, 08GV, the relevant Stacks labels and support/excision terminology, and searched the blueprint for `etale excision`, `supported`, `08GG` and `extension by zero`. Existing nodes supply the exact sum sequence, sum stalks, conservative points, chart calculus, and Hom Mayer–Vietoris. They are cited instead of duplicated. No blueprint node found states this complete structure-sheaf assertion.

## Review by NQ

I read Stacks `spaces-perfect.tex`, Tag 08GG (`lemma-pushforward-with-support-in-open`), its two parts and full proof. I also read 08GV (`lemma-exact-sequence-lower-shriek`), 08GW (`lemma-exact-sequence-j-star`), 08H9 (`lemma-mayer-vietoris-hom`), 08GE (`lemma-restrict-direct-image-open`) and 08HA (`lemma-restrict-lower-shriek`). For the actual unit rather than an arbitrary isomorphism, I read `sites-modules.tex` 03DI (`lemma-extension-by-zero`), 03DJ (`lemma-extension-by-zero-exact`) and 0710 (`lemma-stalk-j-shriek`), and `sites-cohomology.tex` 08FJ (`lemma-adjoint-lower-shriek-restrict`). The geometric-stalk detection source is `spaces-properties.tex` 04K5 (`theorem-exactness-stalks`). Tag/label associations were checked against `tags/tags`. No SGA source is used.

For each step I opened the statements it cites, rather than taking an intermediate fact from a cited node's proof:

1. `lem-sfb-space-elementary-shriek-exact` states exact restriction, exact module sum-extension and their specified adjunction. The exact-functor factorization node gives termwise derived functors and their shift comparisons. `def-weil-exact-derived-adjunction` is used for its specified localized adjunction and its unit normalization, as a definition, not for an unrelated theorem. The chart-calculus statement explicitly gives the canonical derived pullback/direct-image adjunction and identifies etale pullback with exact restriction.
2. The module-forgetful node really preserves kernels and cokernels, and the conservative-geometric-points node really preserves finite limits and small colimits. The passage to exact module stalks is written out through kernels and quotient coequalizers. Exactness commutes with cohomology by the displayed kernel/image calculation. These are elementary consequences of the cited statements and the definition of the derived category, not an appeal to a scheme-only Zariski stalk theorem.
3. The sum-stalk node applies to arbitrary structure-sheaf modules on algebraic spaces and arbitrary representable etale maps, with no finite-fibre hypothesis. The geometric-point comparison node identifies restricted stalks. The reduced-support statement supplies a closed immersion after scheme base change and the correct underlying preimage. Over a field, nonempty support forces its ideal to be zero; the assumed isomorphism over Z then gives exactly one lift. I did not assert reducedness for an arbitrary base change.
4. The extension presheaf and localized module adjunction have the actual sum construction used here; the sum-stalk statement includes the explicit germ formula. I wrote out the unit's section formula and its stalk formula. Its cohomology map is the identity on the singleton fibre over the complement, and zero-to-zero over U. This proves the specified unit, including its normalization.
5. The chart-calculus statement explicitly permits every unbounded complex and every etale base change. The square with base U has source T, and its restricted complex is zero by the given hypothesis. No properness, quasi-coherence or boundedness is introduced.
6. The Hom Mayer–Vietoris statement is for arbitrary pairs of unbounded complexes on this same elementary square, with its middle map equal to restriction. Setting only the second argument to a supported complex kills the U term and both adjacent overlap terms, so no support assumption on A is needed. The triangle identity identifies this actual restriction map with postcomposition by the right-adjunction unit. The inverse is constructed using surjectivity at RPB and injectivity at B; no unstated full-faithfulness theorem is invoked.
7. I checked the types of every composite. The comparison is R(alpha inverse) after the right unit at E = p_!F. Naturality of the right counit and its triangle identity give the explicit transpose equation in the proof. Thus it is the required canonical comparison, and that equation also proves invertibility of the specified counit. The construction is natural on the supported full subcategory.
8. Precomposition with that comparison and the left adjunction give the displayed Hom bijection. The exact-factorization statement supplies the shift comparison for every integer, including negative shifts. This proves the specified bijection and its naturality rather than merely an equality of Hom-set cardinalities.

I tested the extreme cases U = X (then F = 0), U empty (then p is an isomorphism over X_red, and the geometric fibre argument still has a singleton), the identity map, empty spaces, and etale maps with additional components entirely over U. Infinitely many lifts over U cause no problem: every summand is zero; away from U there is exactly one lift. The argument is cohomology-by-cohomology and imposes no bound on the complex. No new statements were introduced to test separately.

Against delivery-errors B–E: there are no new-node form, duplicate, Mathlib-leaf or clause-relabelling issues. The existing notions in the statement are unchanged. Every proof citation is in proof_deps, and every step/node pair has a verbatim quotation. I checked the dependency closures for a path back to this item and found none. The only off-unit ingredients are generic exact-adjunction normalization and exact module-forgetful calculus, declared in split_report.tool_uses. All proof steps are below 2000 characters. The only inline deductions are the displayed stalk/adjunction/zero-Hom calculations from the cited statements; there is no hidden separately assumed geometric lemma.

The required Mathlib searches were made through msearch.py: LeanFinder twice with different formulations, LeanSearch, Loogle and grep. I read the returned hits. The first semantic searches concerned complex-shape support. The second also found Zariski scheme-module open restriction; I inspected `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` around lines 398–450 after a logged grep located its unit formula at line 442. It is a different site, does not cover algebraic spaces or supported derived etale excision, and is not an exact or one-line match. These searches add no claimed Mathlib leaf.

## Unfinished work

None for this one-level stage-1 split. Existing cited unsplit prerequisites remain their own items. No Lean was written or compiled, and no repository or launcher file was edited.
