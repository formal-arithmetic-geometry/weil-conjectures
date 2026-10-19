## Worker report

Item: `lem-coef-quillen-derived-counit-criterion`, stage 2, Q82.

The new module `Sheaf.CategoryTheory.QuillenDerivedCounitCriterion` states
`HomotopicalAlgebra.quillenDerivedCounitCriterion`. Its single theorem has proof
`sorry`. There are no definitions, extra nodes, dependency repairs, statement
corrections, or disputed statements. The item's JSON changes only in `lean`.

Sources read: Hovey, *Model Categories*, Lemma 1.3.10 and its proof (printed
pp. 18–19), Proposition 1.3.13(b)–(c) and proof (pp. 19–20), and the proof of
Corollary 1.3.14 (p. 20), in the PDF named by the node:
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf .
The source explicitly identifies the derived counit with the replacement counit
composite, and the ordinary adjunction transpose with the replacement map.
Also read the current blueprint `main-20261015`,
`sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
paragraph 2 and the following naturality and triangle-identity sentences.
The theorem supplies the ordinary model-category foundation used below that unit;
it does not use its descendant infinity-adjunction result.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Model categories M and N, with the dependency's conventions | `{M : Type uM}`, `{N : Type uN}`, independent `Category.{vM}` / `Category.{vN}`, and `[ModelCategory M]`, `[ModelCategory N]`. The Reedy dependency's `ModelCategory` is Mathlib's class, not a new structure. |
| Complete and cocomplete, as included in the dependency's definition of model category | `[HasLimits M]`, `[HasColimits M]`, `[HasLimits N]`, `[HasColimits N]`. Mathlib's class itself supplies finite limits and colimits, so the full completeness assumptions are retained explicitly, just as in `ReedyModelStructure`. |
| Functorial factorizations in both model pairs | The four `HasFunctorialFactorization` instances, for `(cofibrations, trivialFibrations)` and `(trivialCofibrations, fibrations)` in each category. |
| Ordinary adjunction L ⊣ U | `(L : M ⥤ N) (U : N ⥤ M) (adj : L ⊣ U)`. |
| L preserves cofibrations | `hL`, for every arrow `f` with `Cofibration f`. |
| L preserves trivial cofibrations | `hLt`, for every `f` with both `Cofibration f` and `WeakEquivalence f`, concluding both properties of `L.map f`. |
| Ho(M) and Ho(N), including inversion and the universal property for functors and natural transformations | `HM`, `HN`, `γM`, `γN`, and the two `IsLocalization (weakEquivalences _)` instances. `IsLocalization` is the existing full categorical localization predicate; its precomposition functor is fully faithful and essentially surjective onto functors inverting W. It is not merely the property of inverting W. |
| Cofibrant and fibrant replacements | Existential `Q`, `q : Q ⟶ 𝟭 M`, `R`, `r : 𝟭 N ⟶ R`, and their componentwise object and map properties. Chosen `q` components are trivial fibrations; chosen `r` components are trivial cofibrations, obtained from the assumed functorial factorizations. These are conclusions constructing the replacements, not extra assumptions on M or N. |
| Replacements define LL and RU | Existential `LL : HM ⥤ HN`, `RU : HN ⥤ HM`; `eL : γM ⋙ LL ≅ Q ⋙ L ⋙ γN`, `eU : γN ⋙ RU ≅ R ⋙ U ⋙ γM` identify the actual localized replacement composites. |
| They are left and right derived functors | `α : γM ⋙ LL ⟶ L ⋙ γN` and `β : U ⋙ γM ⟶ γN ⋙ RU`, with Mathlib's `IsLeftDerivedFunctor` and `IsRightDerivedFunctor`. Their component equations with `eL`, `eU`, `q`, `r` specify the usual replacement comparisons, rather than unrelated transformations. These clauses spell out the meaning of the node's derived functors. |
| Derived adjunction LL ⊣ RU | Existential `(d : LL ⊣ RU)`. Its two component equations with `adj.unit` and `adj.counit` identify the adjunction induced by the original adjunction and the derived comparisons. They express which derived adjunction the node means. |
| If LL is an equivalence | The final `LL.IsEquivalence → ...`; this is a condition on the derived functor whose construction has just been specified, never on the original L. All such derived choices are naturally isomorphic, so this property is independent of witnesses. |
| Every fibrant Y | `∀ (Y : N), IsFibrant Y → ...`. |
| Every cofibrant replacement of UY, meaning any weak equivalence with cofibrant source | `∀ (C : M) (q' : C ⟶ U.obj Y), IsCofibrant C → WeakEquivalence q' → ...`. There is deliberately no `Fibration q'` hypothesis. The chosen functorial `q` above and the arbitrary `q'` here are different quantified maps. |
| Its actual counit composite is a weak equivalence | `WeakEquivalence (L.map q' ≫ adj.counit.app Y)`. The composition order in Lean is left-to-right. |
| In particular, if UY is cofibrant, the ordinary counit is a weak equivalence | The final conjunct `∀ Y : N, IsFibrant Y → IsCofibrant (U.obj Y) → WeakEquivalence (adj.counit.app Y)`. |

Dependency declarations and inspected interfaces:

- Statement dependency `lem-coef-reedy-model-structure`: read its entire statement,
  Lean record, and `Sheaf.CategoryTheory.ReedyModelStructure`, especially the complete
  signature and docstring of `HomotopicalAlgebra.Reedy.model_structure` and the
  section variables immediately above it (lines 553–598). That interface uses
  Mathlib's `HomotopicalAlgebra.ModelCategory`, full completeness, and both
  functorial factorization instances, which this theorem uses for M and N.
  The module is publicly imported; the Reedy diagram-construction theorem is not
  itself applied to unrelated diagrams in this ordinary criterion.
- Read `HomotopicalAlgebra.ModelCategory` in
  `Mathlib.AlgebraicTopology.ModelCategory.Basic` (lines 45–88), including its
  weak-factorization-system instances, and `IsCofibrant` / `IsFibrant` in
  `Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant` (lines 33–34 and 81–82).
  These definitions are exactly initial-map cofibrancy and terminal-map fibrancy.
- Read `CategoryTheory.MorphismProperty.HasFunctorialFactorization` in
  `Mathlib.CategoryTheory.MorphismProperty.Factorization` (lines 258–268).
- Read `CategoryTheory.Functor.IsLocalization` and its full precomposition
  interface in `Mathlib.CategoryTheory.Localization.Predicate` (lines 49–55,
  268–282, and the module docstring). The library's canonical `W.Q` satisfies
  this predicate, so choosing arbitrary models of the localization excludes
  none of the node's homotopy categories.
- Read `CategoryTheory.Functor.IsLeftDerivedFunctor` in
  `Mathlib.CategoryTheory.Functor.Derived.LeftDerived` (lines 47–55) and
  `CategoryTheory.Functor.IsRightDerivedFunctor` in
  `Mathlib.CategoryTheory.Functor.Derived.RightDerived` (lines 50–58).
  They use the corresponding Kan-extension universal properties, rather than
  a second private definition of a derived functor.
- Proof dependency `lem-coef-adjunction-equivalence-counit-iso` is a Mathlib leaf:
  read the recorded instance for the counit in
  `Mathlib.CategoryTheory.Adjunction.FullyFaithful` (lines 247–249), and import
  that module non-publicly.
- Proof dependency `lem-coef-brown-split-factorizations` is a Mathlib leaf:
  read both factorization structures and their recorded `Nonempty` instances
  in `Mathlib.AlgebraicTopology.ModelCategory.BrownLemma` (lines 48–87, 97–134).
  Import that module non-publicly.
- Proof dependencies `lem-coef-localized-good-homotopy-test` and
  `lem-coef-model-localization-map-surjective` are Mathlib leaves:
  read their recorded declarations and assumptions in
  `Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma` (especially
  lines 31–34, 65–67, 116–134) and the good-homotopy interfaces in
  `Mathlib.AlgebraicTopology.ModelCategory.Homotopy` (lines 100–119).
  Import `FundamentalLemma` non-publicly; it brings in the homotopy module.
  No proof-dependency import has been omitted for an import cycle.

Edge cases checked before finalizing the statement:

- The arbitrary replacement `q'` may be a weak equivalence that is not a
  fibration. The comparison lift uses only the chosen replacement's trivial
  fibration, exactly as proof step 11 says.
- When `U.obj Y` is cofibrant, its identity is an allowed arbitrary replacement;
  its composite simplifies to the ordinary counit. The separate concluding
  clause keeps this consumer-facing case explicit.
- Fibrancy of Y is retained. No fibrancy of C, all-objects-cofibrant premise,
  properness, pointedness, enrichment, or combinatoriality is assumed.
- Terminal categories, including the zero-category case, allow identity
  replacements and identity counits. Completeness already rules out an empty
  object category, as intended in the source, without a new nonemptiness premise.
- M, N, HM, HN each have independent object and morphism universes, all named
  explicitly. No equality between source, target, and localization universes
  is imposed. The canonical localization is available at the required enlarged
  morphism universe. There are no tests indexed in an accidentally smaller
  independent universe and no finite-size restriction.
- The two unit/counit normalization equations have their standard orientations,
  matching `Adjunction.derived'` in Mathlib's derived-adjunction module. They
  prevent substituting an arbitrary unrelated adjunction between LL and RU.

Searches actually run:

1. `msearch.py ... leanfinder "A Quillen adjunction induces a derived adjunction
   on homotopy categories and a derived equivalence implies the replacement
   counit is a weak equivalence"`: successful, eight hits. The principal hits
   are `CategoryTheory.Adjunction.derived`, `derived'`, `derived_counit`, and
   `derivedε` in `Mathlib.CategoryTheory.Functor.Derived.Adjunction`. Read the
   source and signatures: these are general categorical derived-adjunction
   constructions assuming the derived-functor inputs; they do not construct
   model-category replacements or state the weak-equivalence criterion here.
2. `msearch.py ... loogle 'Quillen, "counit"'`: successful response with zero
   hits and diagnostic `unknown identifier 'Quillen'`. This query is
   inconclusive, not evidence that no theorem exists.
3. `msearch.py ... grep 'Quillen|quillen|derivedAdjunction|derived_adjunction'
   AlgebraicTopology`: successful, 25 hits, mostly reference citations and
   the simplicial-set Quillen model structure. No exact adjunction criterion.
4. `msearch.py ... leansearch "Quillen adjunction derived counit weak equivalence
   for fibrant objects when left derived functor is an equivalence"`:
   successful, eight hits; again general derived-adjunction transformations
   and the total-left-derived comparison, not this model-category theorem.
5. Direct `rg` over the named Mathlib `AlgebraicTopology` and `CategoryTheory`
   sources for `Localization`, `Cofibrant`, `Fibrant`, `Quillen`, derived
   adjunctions and counits located the reused APIs; opened the relevant files.
6. Direct `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for
   `quillen|Quillen|derivedCounit|derived_counit`, and upstream node-id grep:
   no exact ordinary criterion. The project has
   `quillenAdjunctionInfinityLocalization` in `ModelInfinityDerivedAdjunction`,
   which is a different, homotopy-coherent theorem with additional infinity
   localization inputs and does not state the present ordinary criterion.
   Opened its complete signature and docstring; it is not used here.
7. Direct `rg` of the proposed full declaration name in Mathlib, upstream
   `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
   found no declaration-name collision. The upstream names index also has
   no `quillen`/`Quillen`/derived-counit declaration.

Validation: `scompile.py Q82 lem-coef-quillen-derived-counit-criterion
lean/Sheaf/CategoryTheory/QuillenDerivedCounitCriterion.lean` passed in both
sandbox and library-module forms (about 1.3 s / 1.2 s), with no errors or
warnings. All variables and universes are explicit; the module disables
`autoImplicit` and `relaxedAutoImplicit`. The main docstring carries all twelve
DAG proof steps, including the independent saturation argument that avoids a
cyclic dependency. Only the named theorem is postponed.

## Second reading by Q82

I read the item node, its Hovey source place (Lemma 1.3.10, Proposition
1.3.13(b)--(c), and the proof of Corollary 1.3.14, printed pages 18--20), and
the recorded dependency declarations. The node's statement decomposes as
follows; the corresponding Lean rendering and verdict are given for each item.

1. Two independent model categories with complete/cocomplete structure,
   model classes, and functorial factorizations: `{M : Type uM}`, `{N : Type
   uN}`, the independent `Category` universes, `[ModelCategory M/N]`, the four
   `HasLimits`/`HasColimits` instances, and the four
   `HasFunctorialFactorization` instances. This is the same model-category
   foundation as `lem-coef-reedy-model-structure`; no finiteness, pointedness,
   properness, or universe equality is added. Verdict: match.
2. An ordinary adjunction `L ⊣ U`: `(L : M ⥤ N) (U : N ⥤ M) (adj : L ⊣ U)`.
   Verdict: match.
3. Preservation of cofibrations and trivial cofibrations by `L`: `hL` preserves
   `Cofibration`, while `hLt` assumes `Cofibration f` and `WeakEquivalence f`
   and returns both properties for `L.map f`. Verdict: match, with no stronger
   preservation premise.
4. Homotopy-category localizations, inverting weak equivalences and carrying
   the universal property for functors and natural transformations: `γM`,
   `γN` and `[γM.IsLocalization (weakEquivalences M)]`, respectively
   `[γN.IsLocalization (weakEquivalences N)]`. Verdict: match.
5. Functorial cofibrant and fibrant replacements: `Q`, `q`, `R`, `r`, with
   `IsCofibrant (Q.obj X)`, `Fibration (q.app X)`, and `WeakEquivalence (q.app
   X)`, and dually `IsFibrant`, `Cofibration`, and `WeakEquivalence` for `r`.
   These are existentially constructed conclusions, not extra hypotheses.
   Verdict: match.
6. Replacement definitions of the derived functors: `LL`, `RU`, with
   `eL : γM ⋙ LL ≅ Q ⋙ L ⋙ γN` and `eU : γN ⋙ RU ≅ R ⋙ U ⋙ γM`. Verdict:
   match, including orientations.
7. Left and right derived universal properties and their replacement
   comparisons: `α`, `β`, the two `IsLeftDerivedFunctor`/
   `IsRightDerivedFunctor` clauses, and the displayed component equations.
   Each composition is typed in the source-to-target order required by the
   node. Verdict: match.
8. A derived adjunction `LL ⊣ RU`: `(d : LL ⊣ RU)`, together with the unit
   and counit equations relating `d` to `adj`, `α`, and `β`. Verdict: match;
   these equations identify the intended derived adjunction rather than an
   unrelated one.
9. If `LL` is an equivalence, every fibrant `Y` and every cofibrant-source
   weak-equivalence replacement `q' : C ⟶ U.obj Y` has weak-equivalence
   composite `L.map q' ≫ adj.counit.app Y`. Lean quantifies `C`, `q'`,
   `IsCofibrant C`, and `WeakEquivalence q'` in that order and imposes no
   fibration condition on `q'`. Verdict: match.
10. The specialization when `U.obj Y` is cofibrant gives
    `WeakEquivalence (adj.counit.app Y)`, still under fibrancy of `Y` and
    equivalence of `LL`. Verdict: match.

The edge cases are covered: the identity replacement handles a cofibrant
`U.obj Y`; arbitrary replacements need not be fibrations; zero or terminal
model categories are permitted; no nonempty index or object assumption is
introduced; `M`, `N`, `HM`, and `HN` retain independent object and morphism
universes; and no characteristic, Noetherian, or finiteness condition occurs.

I independently searched with `msearch.py`/LeanFinder for a derived Quillen
counit criterion, searched Mathlib and both project trees with `rg` for
`Quillen`, `quillenDerivedCounitCriterion`, and derived-counit criteria, and
checked Mathlib's `Adjunction.derived*`, `IsLeftDerivedFunctor`,
`IsRightDerivedFunctor`, `ModelCategory`, `IsCofibrant`, and `IsFibrant`
signatures. The general categorical derived-adjunction declarations do not
construct replacements or prove this criterion. No duplicate declaration was
found. I also verified the dependency interfaces for
`lem-coef-reedy-model-structure`, the four Mathlib proof leaves, and the
localization/homotopy APIs; each supplies exactly the notion used here.

No mismatch was found, so no Lean or node repair was needed. The node's
`lean.statement` is byte-for-byte equal to the theorem signature in the module.
The module compiles cleanly with the required `scompile.py` wrapper; the only
postponed proof is the named theorem `HomotopicalAlgebra.quillenDerivedCounitCriterion`.
