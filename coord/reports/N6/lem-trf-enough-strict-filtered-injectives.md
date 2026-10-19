## Worker report

The retained stage-1 split packet had no node copy, module, or report, so I reconstructed the delivery from the current shared node. The stage-2 module states the item as `CategoryTheory.FilteredObject.enough_strict_filtered_injectives` using the live `FilteredObject`, `DecreasingFiltration`, `Injective`, and `EnoughInjectives` declarations. Its proof is intentionally `sorry`.

The extension clause has no `EnoughInjectives` assumption. The embedding and prescribed-bound clauses are implications from `EnoughInjectives C`. Strictness is rendered as equality of the image of each filtered step with the meet of the image of the whole map and the target step. Filtered injectivity is the pointwise predicate `Injective (I.filtration.gradedPiece p)`. The finite condition is the recorded `DecreasingFiltration.IsFinite` predicate, and prescribed bounds use `step a = ⊤` and `step (b+1) = ⊥`.

## Second reading by N6

The source was read at `literature/stacks-project/derived.tex`: the definition of filtered injective immediately before Tag 05TP, Tag 05TP (`lemma-filtered-injective`), Tag 05TR (`lemma-injective-property-filtered-injective`), and Tag 05TS (`lemma-strict-monomorphism-into-filtered-injective`). The node's `Fil^f(𝒜)` convention means X, Y, and I in the extension clause are finite filtered objects; the final signature now carries `X.filtration.IsFinite`, `Y.filtration.IsFinite`, and `I.filtration.IsFinite` explicitly.

Clause checklist against the Lean:

1. The abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`. Finite filtered objects and filtration-preserving maps are `FilteredObject C` and its category morphisms, using the recorded upstream `DecreasingFiltration` and SHEAF's `HomPreservingSteps`. A monomorphism is `[Mono u.hom]`; strictness is the equality `imageSubobject ((X.filtration.step p).arrow ≫ u.hom) = imageSubobject u.hom ⊓ Y.filtration.step p` for every integer p, exactly `u(F^pX)=u(X)∩F^pY`. Filtered injectivity is `∀ p, Injective (I.filtration.gradedPiece p)`, where `gradedPiece` is the recorded quotient `F^p/F^(p+1)`. The first conjunct quantifies a filtration-preserving `f : X ⟶ I` and produces filtration-preserving `g : Y ⟶ I` with `u ≫ g = f`; it has no `EnoughInjectives` premise.
2. The enough-injectives embedding clause is `EnoughInjectives C → ∀ X, X.filtration.IsFinite → ∃ I v`, with `Mono v.hom`, the same strictness equality, and pointwise injective graded pieces. This is Tag 05TS and does not add Noetherian, Grothendieck, finiteness-of-homs, or universe restrictions.
3. The same-interval clause is the final conjunct: under `EnoughInjectives C`, for `a ≤ b` and `step a = ⊤`, `step (b+1) = ⊥`, the witness has the same two bounds in addition to strictness, monicity, and filtered injectivity. The inequalities and integer quantifier are unchanged.

The recorded dependency interfaces were opened: Mathlib `CategoryTheory.Abelian`, Mathlib `CategoryTheory.Injective`/`EnoughInjectives`, and the project's `CategoryTheory.DecreasingFiltration`, `FilteredObject`, `HomPreservingSteps`, `step`, `gradedPiece`, and `IsFinite`. No private replacement of these notions is used. The downstream `Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel` was read only to confirm it consumes this exact extension and embedding interface; it does not already declare this item.

Edge cases checked: the zero object and zero filtration (the finite and same-bound clauses permit `⊤ = ⊥`), a single step `a = b`, zero intermediate graded pieces, negative bounds, all filtration indices outside `[a,b]`, and strictness at the boundary indices. The first clause remains valid without enough injectives, as required by Tag 05TR. No characteristic, nonemptiness, Noetherian, or Grothendieck assumption is present, and `u` and `v` are independent category/universe parameters.

Searches run for this second reading:

- `msearch.py ... leanfinder "finite filtered objects have enough injectives for strict monomorphisms"`: eight hits, all ordinary Grothendieck/injective APIs; no exact filtered statement.
- `msearch.py ... leanfinder "a map from a finite filtered subobject into an object with injective graded pieces extends over a strict monomorphism"`: eight ordinary injectivity hits; no exact match.
- `msearch.py ... loogle "CategoryTheory.FilteredObject, CategoryTheory.Injective, DecreasingFiltration"`: no hits (unknown `DecreasingFiltration` in the combined pattern).
- `msearch.py ... loogle "CategoryTheory.Injective, CategoryTheory.Subobject, imageSubobject"`: no hits (unknown `imageSubobject` in the combined pattern).
- `msearch.py ... grep "filtered.{0,30}injective|injective.{0,30}filtered" CategoryTheory`: six irrelevant Mathlib hits about filtered indexing and injective colimits.
- Repository, SHEAF, and slopmaster2 `rg` searches for filtered-injective/strict-monomorphism vocabulary found only downstream consumers and generic filtration APIs; no declaration of this theorem.

The only repair from the reconstructed first draft was adding the finite-filtration hypotheses to the extension clause, because the Stacks source works in `Fil^f(𝒜)` throughout. No node statement correction, dependency repair, or `STATEMENT-DISPUTED` flag is needed. The module compiles cleanly with `scompile.py`; the theorem proof is intentionally `sorry`.

## Maintainer fix (independent review)

The second clause (Tag 05TS) now also concludes `I.filtration.IsFinite`. In Stacks the witness `I` is an object of `Fil^f(𝒜)`, and the node uses finite filtrations throughout. Without this conjunct, clause 2 was weaker than the node and its witness could not be passed to clause 1, which assumes `hI : I.filtration.IsFinite`. No other change. The fixed module compiles cleanly with `nt_compile.py`.
