## Files written

- `dag/nodes/sec-nagata-compactification/def-nagata-scheme-theoretic-image.json`: definition, Mathlib leaf. Applied its current `blueprint_update` verbatim and supplied a match for every clause. Zero new nodes; one Mathlib leaf (the item).
- `citations.json`: `[]`, since this definition/Mathlib leaf has no proof steps or proof citations.

## Attachments

None. The search of `lean/WeilConjectures/` for the literal node id (including its docstring tag) found no declaration. Searches by scheme-theoretic image, density, closure and `Hom.ker` found project lemmas such as `Scheme.Hom.ker_toImage` and base-change comparisons, not a project declaration stating every clause of this definition. The recorded `lean` name is in Mathlib, so it is a leaf rather than a project attachment. The inherited `lean` and audit metadata were preserved.

## WANTED

None. All sources used were available locally.

## Statement correction — STATEMENT-DISPUTED

The imported statement, unlike its main-20261015 update, called the image the *largest* closed subscheme through which a map factors. That is false: for the closed origin `Spec(k) → Spec(k[t])`, both the origin and the whole affine line are closed factorizations; the largest is the whole line, whereas the intended image is the origin. The image is the smallest closed factorization, corresponding to the largest admissible ideal.

The imported unconditional use of the ordinary sheaf kernel is also invalid. I read Stacks `literature/stacks-project/examples.tex`, Tag 0GIK, label `examples-section-scheme-theoretic-image`: let `Y = Spec(k[t])` and `T = ∐_{n≥1} Spec(k[t]/(t^n))`. The ordinary kernel K has K(Y) = ∩(t^n) = 0, but K(D(t)) = k[t,t⁻¹], since the inverse image of D(t) is empty. Hence K is not quasi-coherent (a quasi-coherent ideal zero on this affine's global sections would be zero on D(t)). Its largest quasi-coherent subideal is zero, and the scheme-theoretic image is Y. This verifies the need for the corrected kernel definition without adding a quasi-compactness hypothesis to the morphism itself.

I replaced the item's statement exactly by the existing `blueprint_update.statement`, from `literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/sk-lem-nagata-sketch-closure/def-nagata-scheme-theoretic-image.md`, order 73. The source path now names this snapshot, and the historical blueprint/import fields remain untouched. No target or unit statement was changed.

## Density convention and source comparison

I read Stacks `morphisms.tex`, Tags 01R6 (`morphisms-lemma-scheme-theoretic-image`), 01R7 (`morphisms-definition-scheme-theoretic-image`), and 01R8 (`morphisms-lemma-quasi-compact-scheme-theoretic-image`). These support the corrected ideal/image construction and the ordinary-kernel identification under quasi-compactness, without quasi-separatedness.

I also read Tags 01RB–01RD, labels `morphisms-definition-scheme-theoretically-dense`, `morphisms-example-scheme-theretically-dense-not-dense`, and `morphisms-lemma-scheme-theoretically-dense-quasi-compact`. The current blueprint deliberately uses Mathlib's predicate `ker(g) = 0` for arbitrary morphisms. This must not silently be identified with injectivity of the ordinary structure-sheaf map in the non-quasi-compact case. In the 0GIK example above `g.ker = 0`, although the ordinary sheaf map is not injective over D(t). Stacks' open-subscheme density convention in 01RB is local on all opens and is stronger without quasi-compactness. The blueprint's own general-morphism convention is preserved exactly, while its quasi-compact open-immersion version agrees with the existing `def-nagata-scheme-theoretically-dense-open` leaf.

## Mathlib searches and clause matches

Six searches ran through the required `batch2/msearch.py`, and their exact tool/query records are in `mathlib_searches` and `searches.jsonl`. LeanSearch and LeanFinder both returned `Scheme.Hom.image`, `imageι`, and `toImage`; LeanFinder also returned `Hom.ker`. Loogle returned `Hom.toImage_app`. The three grep searches supplied the kernel construction, the component-kernel equality, the factorization equality, the zero-ideal image criterion, and the density class. None of the services was unavailable. The density grep's single-file output used line numbers in its `file` column; I checked the actual source with numbered reads instead of treating that formatting as a declaration path. Search results were checked in the pinned local source, not accepted from their generated summaries.

The `mathlib_match.how` records the full names, files and source lines clause by clause:

- `AlgebraicGeometry.Scheme.Hom.ker`, `Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:692`, uses `IdealSheafData.ofIdeals` at line 104. Its `le_ofIdeals_iff` at 125 is precisely the largest-ideal characterization, rather than a separately unproved equivalence. `Hom.ker_apply` at 702 supplies the ordinary-kernel equality on the affine basis when the morphism is quasi-compact.
- `AlgebraicGeometry.Scheme.Hom.image` and `imageι`, `Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:662,665`, are literally the closed subscheme of the kernel ideal and its inclusion. `toImage` at 710 and `toImage_imageι` at 715 supply its factor map and composite equality for arbitrary morphisms.
- `AlgebraicGeometry.IsSchemeTheoreticallyDominant`, `Mathlib/AlgebraicGeometry/Morphisms/SchemeTheoreticallyDominant.lean:38`, is exactly the predicate `g.ker = ⊥`. `AlgebraicGeometry.Scheme.isIso_subschemeι_iff_eq_bot`, `Subscheme.lean:735`, identifies this with the closed image being the entire target, interpreted as an isomorphism of closed subschemes, not literal equality of separately constructed scheme objects.
- The closure clause is the one-line specialization `Scheme.Hom.image i` to the immersion i presenting the locally closed subscheme. It introduces no new theorem about restriction or topological closure, and claims neither of those properties without quasi-compactness.

## Existing-node and blueprint search

`python3 tools/blueprint_refs.py search 'scheme-theoretic image'` searched the whole blueprint index and returned 23 nodes; `ancestor def-nagata-scheme-theoretic-image` confirmed the item itself is the blueprint ancestor. The DAG text search included image, density, kernel ideal, closure, and the relevant existing Mathlib declaration names. I opened `lemma-nagata-scheme-image-ideal-qc`, `def-weil-pbc-scheme-conventions`, `def-nagata-scheme-theoretically-dense-open`, `def-nagata-scheme-theoretic-closure`, and `def-nagata-scheme-image-factor`. The first supplies the image/factor construction named in this item's statement, but does not purport to define the general density predicate. The density-open node only treats quasi-compact open immersions; closure and factor nodes each name a clause, not the entire bundled definition. No additional node is created for any of those clauses. No other blueprint node states this entire bundle, so `blueprint.same_as` is `[]`.

## Not duplicates

No new nodes were created. Existing closure, factor, and quasi-compact-open density nodes were read and left unchanged; they are not repeated by new nodes.

## Review by Q92

I compared the item's corrected text against the main-20261015 definition line by line and against the kernel/image construction in Stacks 01R6–01R8. I read the chapter and unit records before matching it: this is the definition used by the closure unit's kernel/image step, not the key node realizing all the unit's compactification assertions. Therefore the unit record is not edited, and no alternative compactification route is substituted.

For the kernel clause I checked both directions of the maximality characterization in `ofIdeals`/`le_ofIdeals_iff`; the kernel is an actual supremum construction, not chosen from a bare existence claim. `ker_apply` requires only quasi-compactness and has that hypothesis precisely where the parenthesis uses it. For the image, inclusion and factor map I checked that the ambient target is Y, the source is T, and `toImage ≫ imageι = g` has the claimed direction. These definitions and equality do not require quasi-compactness. For the density clause I checked the zero ideal is on Y and that the image is the whole target as a closed subscheme, using the inclusion-isomorphism criterion. For closure I substituted the immersion itself into `Hom.image`, rather than invoking an unproved identification with a topological closure.

There are no proof steps: this item is a definition which matches Mathlib, so C1–C4's step-by-step proof citations are empty and `citations.json` is empty. The retained statement dependencies are the scheme conventions and the existing image-interface statement explicitly named in the corrected definition. I opened their statements; the interface gives the closed immersion and factor map the definition refers to. No step takes a maximality theorem, a restriction theorem, or stalk injectivity from a mere definition. No missing argument is moved to a new node; no non-elementary or long proof step is hidden. All B1–B10 and D1–D5 cases involving new nodes or proof relabelling are thus avoided by this direct Mathlib leaf, with source lines and clause matches supplied as required by B6/B8.

For E1–E7 I tested the identity morphism (zero ideal, full image, dense), empty source to a nonempty scheme (unit ideal, empty image, not dense), the empty target (zero and unit coincide, consistently), the closed origin in the affine line (proper closed image), the nonreduced closed immersion `Spec(k) → Spec(k[ε]/(ε²))` (kernel `(ε)`, hence topological surjectivity is not the density predicate), and the non-quasi-compact disjoint-thickening example above. The last two tests guard against confusing topological and scheme-theoretic density, and the latter explicitly disproves the imported raw-kernel formulation. The only corrected mathematical wording is the already-supplied blueprint update. No SGA reference, Lean edit, compiler invocation, or repository write was used.

## Unfinished work

None in the one-level stage-1 scope. The maintainer's independent mathematical review remains the delivery protocol's next step.
