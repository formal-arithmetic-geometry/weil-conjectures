## Worker report

The returned stage-1 split has been repaired with the Lean module
`Sheaf.CategoryTheory.InjectiveTargetHomSymbol`.  It uses the recorded
`CategoryTheory.DecreasingFiltration`, `CategoryTheory.FilteredObject`, and
`CategoryTheory.FilteredObject.Hom` declarations.  The module defines the filtered-degree
predicate and the genuine `AddSubgroup` `filteredHomSubgroup`, the quotient-induced shifted
graded component, its additive component map, the finite direct-sum symbol map, and the
canonical additive precomposition/postcomposition maps.  The theorem
`CategoryTheory.FilteredObject.injectiveTargetHomSymbol` states the exact symbol sequence and
both naturality directions, with `sorry` reserved for its proof.

The Lean rendering of each hypothesis and conclusion is as follows.

* The arbitrary abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`; `u` and
  `v` are independent, so no universe restriction is imposed.
* The finite decreasing filtrations are `X Y : FilteredObject C`, with integer bounds
  `a ≤ b`, `c ≤ d` and equations `X.filtration.F a = ⊤`,
  `X.filtration.F (b + 1) = ⊥`, `Y.filtration.F c = ⊤`, and
  `Y.filtration.F (d + 1) = ⊥`.
* Injectivity of every target graded piece is
  `hgr : ∀ q : ℤ, Injective (Y.filtration.gr q)`, using Mathlib's extension-property
  `CategoryTheory.Injective`.
* `HasFilteredDegree X Y r f` is the factorisation condition
  `∀ p, ∃ l : F^p X ⟶ F^(p+r) Y, l ≫ arrow = arrow ≫ f`; the subgroup
  `filteredHomSubgroup X Y r : AddSubgroup (X.obj ⟶ Y.obj)` renders `G^r(X,Y)`.
* `shiftedGradedMap` is characterized by the cokernel equation on
  `F^p X/F^(p+1)X` and `F^(p+r)Y/F^(p+r+1)Y`.  Its additive component is
  `shiftedGradedMapHom X Y r p`, and `filteredHomSymbol X Y r a b` is the sum over
  `Finset.Icc a b` in
  `⨁ p : ℤ, (X.filtration.gr p ⟶ Y.filtration.gr (p + r))`.
* The first exactness clause is
  `filteredHomSubgroup X Y (r + 1) ≤ filteredHomSubgroup X Y r`.
  The kernel clause is rendered pointwise as
  `filteredHomSymbol X Y r a b f = 0 ↔ f.1 ∈ filteredHomSubgroup X Y (r + 1)`.
  Surjectivity is `Function.Surjective (filteredHomSymbol X Y r a b)`.  Together these
  are the displayed `0 → G^(r+1) → G^r → ⨁ Hom(gr^p X,gr^(p+r)Y) → 0` sequence.
* Precomposition naturality quantifies `u : FilteredObject.Hom X' X` for every finite
  filtered `X'` and states, component by component,
  `shiftedGradedMapHom X' Y r p (precompHom ... u f) =
   FilteredObject.gradedMap u p ≫ shiftedGradedMapHom X Y r p f`.
* Postcomposition naturality quantifies finite `Y'` with
  `∀ q : ℤ, Injective (Y'.filtration.gr q)` and `v : FilteredObject.Hom Y Y'`, and states
  `shiftedGradedMapHom X Y' r p (postcompHom ... v f) =
   shiftedGradedMapHom X Y r p f ≫ FilteredObject.gradedMap v (p + r)`.

The recorded dependency declarations used are:

* `CategoryTheory.Abelian` (Mathlib, `Mathlib/CategoryTheory/Abelian/Basic.lean`),
  the abelian-category structure;
* `CategoryTheory.DecreasingFiltration` (upstream module
  `WeilConjectures.CategoryTheory.Abelian.Filtration`), with its `F`, `F_succ_le`,
  `antitone`, and `gr` operations;
* `CategoryTheory.Injective` (Mathlib,
  `Mathlib/CategoryTheory/Preadditive/Injective/Basic.lean`), the extension-property
  injectivity predicate;
* `CategoryTheory.FilteredObject.injective_graded_filtration_splits` from
  `Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits`, imported for the four-step proof
  recorded in the theorem docstring.

Edge cases checked before writing: `a = b` and `c = d` (one graded layer), `X` or `Y` the
zero object, `r` outside the filtration intervals (the direct-sum interval still gives the
zero symbol components), and empty/out-of-range graded pieces.  The integer index is all of
`ℤ`; the hypotheses do not exclude negative shifts or zero-length intervals.

Searches made:

* `msearch.py ... leanfinder "filtered Hom symbol map for finite decreasing filtrations with injective graded target"`: eight hits, all module/ring filtrations or ordinary injective resolutions; no matching declaration.
* `msearch.py ... loogle "CategoryTheory.DecreasingFiltration, CategoryTheory.FilteredObject, CategoryTheory.Injective"`: zero hits because the project filtration declaration is upstream rather than Mathlib.
* `msearch.py ... grep "symbol.*filtered|filtered.*Hom" CategoryTheory`: 25 hits, all filtered-index categories or unrelated Hom constructions; no symbol-sequence theorem.
* `rg` over `WeilConjectures/` and `lean/Sheaf`: no existing `injectiveTargetHomSymbol`, `filteredHomSymbol`, or `HasFilteredDegree` declaration before this module.
* The dependency node records and their full source signatures/docstrings were read, including the split lemma's `FilteredObject` interface.

The per-file `scompile.py` check completed successfully for the sandbox module and the
library overlay (no errors or warnings).

## Second reading by Q16

I reread the node statement against Stacks Tag 05TP and the four recorded proof steps.  The
module retains arbitrary abelian-category universes, uses the recorded filtration and graded
quotient objects, makes `G^r` an actual additive subgroup, and states the inclusion, kernel,
surjectivity, precomposition, and postcomposition clauses separately.  The base
`split_report.summary` is unchanged; only the `lean` field was added to the node copy.
