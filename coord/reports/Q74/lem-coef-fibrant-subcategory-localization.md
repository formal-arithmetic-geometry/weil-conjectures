## Worker report

The module `Sheaf.CategoryTheory.FibrantSubcategoryLocalization` states
`HomotopicalAlgebra.fibrant_subcategory_localization`. It uses the landed
`HomotopicalAlgebra.FiniteReedy.IsLocalization` definition, recorded independently
by `def-coef-coherent-localization-interface`. That definition imposes the exact
full coherent functor-category universal property. The induced comparison uses
`SSet.Enhanced.IsFunctorEquivalence` and `SSet.Enhanced.AreNaturallyEquivalent`.
No finite-Reedy theorem is used and no localization predicate is copied.

The category is `C : Type u` with `[Category.{v} C]`; `one : C` and
`hone : IsTerminal one` provide the terminal maps `hone.from X`. The weak and
fibration classes are `W P : MorphismProperty C`. The hypotheses render the node
clause by clause as follows:

* `hWiso` and `hPiso` say that every isomorphism belongs to `W` and `P`.
* `hWcomp` and `hPcomp` say that each class is closed under composition.
* `hWtwo : W.HasTwoOutOfThreeProperty` is the two-out-of-three hypothesis for `W`.
* `hpullback` quantifies `p : X ⟶ Y` in `P` and `v : Y' ⟶ Y` with `X`, `Y`, and
  `Y'` fibrant (`P (hone.from _)`). It supplies a pullback object `X'`, maps
  `a : X' ⟶ X` and `b : X' ⟶ Y'`, `IsPullback a b p v`, fibrancy of `X'`,
  `P b`, and the implication `W p → W b`.
* `hfactor` quantifies every `f : X ⟶ Y` whose codomain is fibrant and supplies
  `X'`, `w : X ⟶ X'`, and `p : X' ⟶ Y` with `W w`, `P p`, fibrant `X'`, and
  `w ≫ p = f`. It makes no functoriality assumption.
* The conclusion supplies coherent-localization maps `qf` for the full
  subcategory on `P (hone.from X)` and `q` for `C`, both with the shared
  `HomotopicalAlgebra.FiniteReedy.IsLocalization` predicate;
  `e : Lf ⟶ L` is an `SSet.Enhanced.IsFunctorEquivalence`, and
  `SSet.Enhanced.AreNaturallyEquivalent (qf ≫ e) (i ≫ q)` records coherent
  compatibility with the canonical nerve inclusion
  `i = SSet.uliftFunctor.map (nerveMap (ObjectProperty.ι ...))`.
  The restricted class is exactly
  `W.inverseImage (ObjectProperty.ι (fun X : C ↦ P (hone.from X)))`.

Dependency declarations used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declaration
  `SSet.Enhanced.IsFunctorEquivalence` and
  `SSet.Enhanced.AreNaturallyEquivalent` (the node dependency
  `def-cbc-enhanced-diagrams-cones`).
* `Sheaf.CategoryTheory.FiniteReedyLocalization`, declarations
  `HomotopicalAlgebra.FiniteReedy.IsLocalization`, `Inverts`, `localDiagrams`,
  and `largeNerve`, through `def-coef-coherent-localization-interface`.
  The definition node is independent of the downstream finite-Reedy theorem.
* Recorded proof inputs `Sheaf.CategoryTheory.SystemLocalizationUniversal` and
  `Sheaf.CategoryTheory.InfinityFullEssentialImage` are non-public proof imports.
  The other two proof nodes currently have no recorded module.
* Mathlib `CategoryTheory.Limits.IsPullback`,
  `CategoryTheory.Limits.IsTerminal`, `CategoryTheory.MorphismProperty`,
  `CategoryTheory.ObjectProperty.FullSubcategory`, `CategoryTheory.nerveMap`,
  and `SSet.uliftFunctor`.

Edge cases checked: the fibrant subcategory contains `one`, since its terminal self-map is the identity
and `hPiso` applies; the supplied terminal object excludes an empty `C`; `W` and `P` may
be the identity/isomorphism classes; `p` may be an isomorphism; `v` is arbitrary
and need not lie in `P`; the pullback implication is vacuous when `p ∉ W`; a
factorization is required only for fibrant codomains; no functorial factorization
or fibrancy of arbitrary objects is introduced. Universe lifts permit the two
ordinary nerves and all target quasicategories to live in the common universe
`SSet.{max u v t}`.

Searches made: the node's recorded `msearch.py` LeanSearch, LeanFinder, Loogle,
and Mathlib grep searches for fibrant-object localization and coherent
localization (all report no exact match); `rg -n "IsLocalization|coherent.*local"
lean/Sheaf` found existing localization interfaces but no fibrant-subcategory theorem;
`rg -n "fibrant_subcategory_localization|coherent localization"
WeilConjectures` found no upstream declaration. Mathlib's
`AlgebraicTopology/ModelCategory/FibrantObjectHomotopy` only gives ordinary model
category localization instances and does not state the Brown coherent
functor-category result, so no existing declaration matches the node.

No `STATEMENT-DISPUTED` flag or node fault was found. The module compiled cleanly
with `scompile.py`; the only proof placeholder is the theorem's required `sorry`.

## Earlier second reading (a previous round; superseded)

I reread the node and the generated signature independently. Every source
hypothesis has one corresponding binder above, and every conclusion clause is
present: both coherent localizations, restriction of `W` to the full fibrant
subcategory, the induced map, its functor equivalence, and coherent commutation
with the nerve inclusion. The pullback maps have the stated orientation
`X' ⟶ X` and `X' ⟶ Y'`, and the factorization has the stated order
`X ⟶ X' ⟶ Y`. No extra fibrancy, functoriality, nonemptiness, or model-category
assumption is present.

## Second reading by Q74

I read the node statement as the following list and matched each item to the Lean signature.

* The ambient object is an ordinary category `C : Type u` with `[Category.{v} C]`, a
  chosen terminal object `one : C`, and `hone : IsTerminal one`. The Lean declaration
  has exactly these binders; the ordinary nerve is used as required by the node.
* `W` and `P` are arrow classes. `hWiso` and `hPiso` put every isomorphism in the
  respective class, and `hWcomp` and `hPcomp` give closure under composition. These
  are exactly the node's class hypotheses, with no extra finiteness or model-category
  structure. `hWtwo : W.HasTwoOutOfThreeProperty` is the node's two-out-of-three
  hypothesis.
* Fibrancy is rendered as `P (hone.from X)`. For `p : X ⟶ Y` in `P` and
  `v : Y' ⟶ Y`, with `X`, `Y`, and `Y'` fibrant, `hpullback` supplies `X'`,
  `a : X' ⟶ X`, `b : X' ⟶ Y'`, `IsPullback a b p v`, fibrancy of `X'`, `P b`, and
  `W p → W b`. The orientations and all four fibrancy conditions agree with the
  source and node; `v` is correctly unrestricted.
* For every `f : X ⟶ Y` with fibrant codomain, `hfactor` supplies
  `X'`, `w : X ⟶ X'`, and `p : X' ⟶ Y`, with `W w`, `P p`, fibrant `X'`, and
  `w ≫ p = f`. This preserves the nonfunctorial factorization and does not require
  arbitrary objects to be fibrant. The explicit intermediate fibrancy clause is the
  clause stated in the node (and follows from the source's composition axiom).
* The conclusion supplies `Lf`, `L`, `qf`, `q`, and `e : Lf ⟶ L`. The shared predicates
  `HomotopicalAlgebra.FiniteReedy.IsLocalization` on `qf` and `q` express the full
  coherent functor-category universal property from the node, including all higher
  transformations. The restricted class is exactly
  `W.inverseImage (ObjectProperty.ι (fun X : C ↦ P (hone.from X)))`; `e` is an
  `SSet.Enhanced.IsFunctorEquivalence`; and the final clause is the coherent
  equivalence between `qf ≫ e` and the nerve inclusion followed by `q`. Quantifier
  order and the universe lift `SSet.{max u v t}` agree with the node.

Edge cases were checked: the full fibrant subcategory contains the terminal
object; the ambient category cannot be empty because `one` is supplied; `W` and `P` may be the
isomorphism or identity classes; `p` may be an isomorphism; `v` need not be in `P`;
the implication `W p → W b` is vacuous when `p` is not weak; and no factorization is
required for a nonfibrant codomain. Empty indexing is not introduced, and no degree,
characteristic, Noetherian, or universe-equality assumption is present.

I searched Mathlib and the project/source with `msearch.py` (LeanSearch, LeanFinder,
Loogle), and with `rg` for fibrant-object localization, coherent localization,
`fibrant_subcategory_localization`, and `IsCoherentLocalization`. Mathlib's
`FibrantObjectHomotopy` gives only ordinary localization under a full model-category
instance; no exact theorem matches. The finite-Reedy theorem is downstream, but the exact localization helper is
recorded independently by the landed definition node
`def-coef-coherent-localization-interface`. The resumed reading below repairs the
old duplicate helpers to use that shared definition without using the theorem.

I read Cisinski, *Higher Categories and Homotopical Algebra*, Definition 7.4.6,
Definition 7.4.12(i)--(ii), Proposition 7.5.16, and Theorem 7.5.18. The ordinary-nerve
specialization in the node is rendered faithfully. The retained reading initially found no mismatch. The resumed review below records
the current-source repairs and supersedes that initial conclusion.

### Resumed second reading, 2026-10-17

I retained the hypothesis-by-hypothesis list above and reopened the current node,
its sandbox module, `def-cbc-enhanced-diagrams-cones` and its actual declarations,
and the independently landed localization definition node and module.
I also reread Cisinski Definitions 7.4.6 and 7.4.12 on printed pp. 360--361,
365--366 and Theorem 7.5.18 on p. 380 at
https://cisinski.app.uni-regensburg.de/CatLR.pdf. There is no Stacks source for
this item. In the ordinary nerve, equivalences are precisely isomorphisms and
mapping spaces are discrete, so the ordinary pullback/terminal hypotheses are
exactly the source hypotheses. There is no added functorial replacement assumption.

Current-source findings and repairs:

* H4: the old `HomotopicalAlgebra.Inverts` and `IsCoherentLocalization` helpers
  duplicated the landed `FiniteReedy` predicates. I removed both helpers and used
  `FiniteReedy.IsLocalization` twice in the conclusion. I added its existing
  definition node to `stmt_deps`, imported its module, and removed the deleted
  helpers from `lean.declarations`. Its `largeNerve` unfolds to precisely the same
  degreewise `uliftFunctor` ordinary nerve. Its `localDiagrams` is the full
  subcomplex on exactly the weak-equivalence-inverting functors; the factoring
  map equals actual precomposition and is a coherent functor equivalence.
  This preserves every conclusion clause and all independent universes.
* H8: the old theorem docstring only summarized Brown replacement and omitted
  the node's proof. I expanded it to all five steps: existence and the comparison,
  essential surjectivity of localization, final localized comma functors, full
  faithfulness by the final-square criterion, and essential surjectivity via
  terminal-arrow fibrant replacement followed by the full-essential-image theorem.
* H9: I added the two currently recorded proof-module imports (system localization
  and full essential image), as non-public imports. The final-square and localized
  comma nodes currently have no recorded declaration and are named in the docstring.
* The old edge-case report incorrectly said the fibrant subcategory may be empty.
  It contains the terminal object because the terminal self-map is the identity.
  I corrected that report; no Lean hypothesis or mathematical node statement changed.

Fresh searches used LeanSearch (localization unchanged on fibrant objects),
LeanFinder (relative category with nonfunctorial fibrant replacements), Loogle
(`"IsLocalizedEquivalence"`), and `rg` of Mathlib, upstream `WeilConjectures`,
project `lean/Sheaf`, and DAG nodes with localization/interface terminology.
The Mathlib results are ordinary model-category localizations (opened
`FibrantObjectHomotopy.lean` and its `ModelCategory` context), so they are not an
exact theorem match. The project search exposed the independent definition-node
interface, which is now reused. There are no new nodes or dependency modules.

I rechecked all binders and the unchanged conclusion data after the replacement:
`C`, `one`, `W`, `P`, `hone`, the isomorphism/composition and two-out-of-three
hypotheses, pullback existence/fibrancy/class membership, and nonfunctorial
factorizations are unchanged. `qf`, `q`, `e`, the restricted arrow class, the
coherent equivalence and its commuting square are unchanged. No variable or universe
is unbound. The node's `lean.statement` was regenerated verbatim from the signature.
The theorem's whole proof remains `sorry`; all constructions used are real definitions.

Validation of the repaired module: prescribed `scompile.py Q74
lem-coef-fibrant-subcategory-localization
lean/Sheaf/CategoryTheory/FibrantSubcategoryLocalization.lean` returned exit 0,
with no diagnostics, compiling the sandbox probe (1.7 s) and the library module
(2.0 s). The exact single-file comparison confirms `lean.statement` equals the
normalized signature, and every Lean line is at most 100 characters.
