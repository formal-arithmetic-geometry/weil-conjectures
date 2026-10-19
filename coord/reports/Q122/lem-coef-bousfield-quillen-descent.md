## Worker report

The module `Sheaf.CategoryTheory.BousfieldQuillenDescent` states
`HomotopicalAlgebra.bousfield_quillen_descent`, with a `sorry` proof. It uses the
same source simplicial model category `M`, arbitrary model target `N`, original
cofibrant replacement `Q`, and the given adjunction `F ⊣ U`. The localized model
structure is represented by the explicit `localized : ModelCategory M` argument.

The Lean statement renders the node as follows. The model-category hypotheses on
`M` and `N`, limits and colimits, and both functorial factorization instances are
bound explicitly. `[SimplicialCategory M]`, `T`, and `hSM7` express the simplicial
model-category structure and SM7 condition. `I : Type w`, `A B : I → M`, and
`s : ∀ i, A i ⟶ B i` encode the small set of arrows, including `I = Empty`.
`Q`, `ε`, and `hQ` encode the chosen functorial cofibrant replacement and its
objectwise weak equivalence. `localized` is the second model structure on the
same underlying category. `hC` identifies its cofibrations with the original
cofibrations. `hW` says exactly that its weak equivalences are the maps inducing
weak homotopy equivalences on original derived mapping spaces into every original
fibrant object satisfying the displayed localizing-arrow condition; the maps are
rendered by `eHomWhiskerRight SSet (Q.map f) Z`. The two localized functorial
factorization instances are bound explicitly. `F`, `U`, and `adj` are the given
ordinary Quillen adjunction data; `hF` and `hFt` state preservation of original
cofibrations and original trivial cofibrations, and `hS` states that `FQ(s i)` is
an original weak equivalence for every `i`. The conclusion gives preservation by
`F` of localized cofibrations and localized trivial cofibrations, which is the
Quillen conclusion for the unchanged adjunction.

Dependency declarations used:

- `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`,
  `HomotopicalAlgebra.ModelInfinity.quillenAdjunctionInfinityLocalization`.
- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`,
  `CategoryTheory.simplicial_model_nerve_localization`.
- `Sheaf.CategoryTheory.QuillenFibrantTest`,
  `HomotopicalAlgebra.quillen_fibrant_test` (proof dependency imported privately).
- `lem-coef-bousfield-local-fibrations` is a proof dependency in the DAG but has no
  landed Lean declaration, so no unavailable import is fabricated in this module.

Edge cases checked: `I = Empty` gives the empty localizing set; singleton and
identity arrows give the expected locality test; `Q = 𝟭 M` with identity replacement
is allowed; the terminal model category and identity adjunction fit the binders;
no nonemptiness, properness, combinatoriality, or simplicial structure on `N` is
introduced. The mapping-space formula uses the original structure and does not
restrict the universe of `I` beyond the stated `Type w`.

Searches made: `msearch.py` LeanSearch query “Left Quillen functors descend to
left Bousfield localized model structures” returned localization and derived-functor
APIs but no model-category descent theorem; Loogle query `"Bousfield"` returned
zero matches; LeanFinder query “A left Quillen adjunction descends through left
Bousfield localization when its derived left functor inverts the localizing arrows”
returned only generic localization/derived-functor declarations; grep of
Mathlib `AlgebraicTopology/ModelCategory` found no descent theorem; grep of
Mathlib and `WeilConjectures/` found no declaration for this item or its theorem
name; grep of `lean/Sheaf` found no existing statement. Mathlib's
`CategoryTheory.Localization.Bousfield` is ordinary categorical orthogonality and
does not state model Bousfield descent.

No statement correction or `STATEMENT-DISPUTED` flag is needed.

## Earlier second reading (a previous round; superseded)

The node's statement was read as the following ordered list and matched against
`HomotopicalAlgebra.bousfield_quillen_descent`.

1. The source model categories `M` and `N`, their categories, model structures,
   limits, colimits, and functorial factorizations are the explicit typeclass
   binders `[Category]`, `[ModelCategory]`, `[HasLimits]`, `[HasColimits]`, and
   the four `HasFunctorialFactorization` binders. These are exactly the model
   category conventions supplied by `lem-coef-model-infinity-derived-adjunction`;
   no properness, combinatoriality, or target simplicial structure is added.
2. The simplicial model structure on `M` is rendered by `[SimplicialCategory M]`,
   `T : SimplicialTensorCotensor M`, and
   `hSM7 : SimplicialModelLocalization.SatisfiesSM7 M`, matching the dependency's
   simplicial and SM7 conventions.
3. The small set of arrows is rendered by `I : Type w`, `A B : I → M`, and
   `s : ∀ i, A i ⟶ B i`; no nonemptiness or finiteness assumption is imposed.
4. The functorial cofibrant replacement is `Q : M ⥤ M`, `ε : Q ⟶ 𝟭 M`, and
   `hQ : ∀ X, IsCofibrant (Q.obj X) ∧ WeakEquivalence (ε.app X)`, so the
   replacement is objectwise cofibrant and weakly equivalent as required.
5. The assumed localized model structure is the explicit `localized :
   ModelCategory M`; `hC` identifies its cofibrations with the original
   cofibrations. `hW` says its weak equivalences are exactly the arrows whose
   original derived mapping-space maps, written as
   `eHomWhiskerRight SSet (Q.map f) Z`, are weak homotopy equivalences for every
   original fibrant `S`-local `Z`, with locality expressed by the corresponding
   condition for every `Q.map (s i)`. This has the node's quantifier order and
   uses the original model structure.
6. The two localized functorial factorization instances are bound explicitly,
   supplying the model-structure infrastructure without changing the stated
   weak-equivalence or cofibration classes.
7. The adjunction data are `F : M ⥤ N`, `U : N ⥤ M`, and `adj : F ⊣ U`.
   `hF` and `hFt` spell out preservation of original cofibrations and original
   trivial cofibrations, exactly the Quillen-adjunction hypothesis in the cited
   dependency; `hS` states that every `F.map (Q.map (s i))` is an original weak
   equivalence.
8. The conclusion has the same adjoint functors and states preservation of
   localized cofibrations and localized trivial cofibrations by `F`, with the
   target conclusions `Cofibration` and `WeakEquivalence`. This is the node's
   Quillen conclusion written in the project's clause-by-clause convention.

Edge cases were checked. `I = Empty` makes the locality condition vacuous; a
singleton, identity, or zero arrow is admitted; `Q = 𝟭 M` with identity
replacement is admitted; and terminal or empty underlying categories and the
identity adjunction introduce no excluded case. Universes `u`, `u'`, `v`, `v'`,
and the independent small-set universe `w` are all explicitly bound, and no
characteristic or nonzero assumption occurs.

The worker's three search kinds were inspected and rerun conceptually against
Mathlib, `WeilConjectures/`, and `lean/Sheaf/`: no exact Bousfield model-category
descent declaration exists. Mathlib's categorical Bousfield localization and
derived-adjunction declarations do not state preservation of the localized
trivial cofibrations. The recorded dependency declarations were opened and
match the uses. The proof-only dependency `lem-coef-bousfield-local-fibrations`
has no landed Lean declaration, so no unavailable import was fabricated; it is
used only in the statement's proof docstring.

No mismatch was found, so no Lean or node change was necessary. The module has
the source place and `(blueprint: lem-coef-bousfield-quillen-descent)` in its
docstrings, contains only the postponed theorem proof, and compiled with
`scompile.py` without errors or warnings beyond the permitted `sorry`.

## Second reading by Q122

I reread the source statement at Hirschhorn, *Model Categories and Their Localizations*,
Proposition 3.3.18(1), p. 63, together with Definition 8.1.2 and Definition 8.1.15
(pp. 138--141), and matched its objects and clauses to the theorem signature.

1. The source model categories \(\mathcal M\) and \(\mathcal N\), with their categories,
   model structures, limits, colimits, and functorial factorizations, are the binders
   `[Category]`, `[ModelCategory]`, `[HasLimits]`, `[HasColimits]`, and the four
   `HasFunctorialFactorization` instances. The two categories are distinct, and no
   target simplicial, proper, combinatorial, or size hypothesis is added.
2. The simplicial model structure on \(\mathcal M\) is rendered by
   `[SimplicialCategory M]`, `T : SimplicialTensorCotensor M`, and
   `hSM7 : SimplicialModelLocalization.SatisfiesSM7 M`. This is the dependency's
   enriched tensor/cotensor and SM7 data.
3. The small set \(S\) of arrows is rendered by `I : Type w`, `A B : I → M`, and
   `s : ∀ i, A i ⟶ B i`. The index is allowed to be empty or any other small type;
   no finiteness or nonemptiness is introduced.
4. The functorial cofibrant approximation is `Q : M ⥤ M`, `ε : Q ⟶ 𝟭 M`, and
   `hQ : ∀ X, IsCofibrant (Q.obj X) ∧ WeakEquivalence (ε.app X)`. This matches the
   source definition of a cofibrant approximation (a weak equivalence with cofibrant
   source); it does not silently require the stronger trivial-fibration variant.
5. The localized model structure is the explicit `localized : ModelCategory M`.
   `hC` identifies its cofibrations with the original cofibrations. `hW` gives the
   exact local-equivalence test: for every original fibrant `Z` satisfying the
   displayed precomposition equivalence for every `Q.map (s i)`, the displayed
   precomposition map for `Q.map f` is a weak homotopy equivalence. The mapping
   spaces therefore use the original model structure and the quantifier order is
   the source's one.
6. The two localized functorial factorization instances are bound explicitly, so
   `localized` is a complete model structure with the required factorizations. They
   do not alter the specified cofibration or weak-equivalence classes.
7. The ordinary adjunction is `F : M ⥤ N`, `U : N ⥤ M`, `adj : F ⊣ U`. `hF` and
   `hFt` state preservation by `F` of original cofibrations and original trivial
   cofibrations, respectively, which is exactly the source's left Quillen input.
   `hS` states that the chosen cofibrant replacement image `F.map (Q.map (s i))`
   is an original weak equivalence for every localizing arrow.
8. The conclusion is the conjunction that `F` preserves localized cofibrations and
   localized trivial cofibrations, with the latter mapped to an original cofibration
   and weak equivalence in `N`. This is precisely the assertion that the unchanged
   adjunction is left Quillen from `localized` to `N`.

No mismatch was found between this list and
`HomotopicalAlgebra.bousfield_quillen_descent`; no Lean or node statement change was
needed. The proof-only local-fibrations dependency has a stronger implementation
interface for a chosen trivial-fibration replacement, but the item correctly follows
the source's weaker cofibrant-approximation definition; obtaining that auxiliary
replacement is a stage-3 proof obligation and is not an extra hypothesis here.

Edge cases were checked explicitly. `I = Empty` gives an empty localizing family and
makes the locality antecedent vacuous; singleton and identity arrows are admitted;
repeated arrows and zero arrows are admitted; `Q = 𝟭 M` with identity augmentation is
admitted when the displayed cofibrancy and weak-equivalence hypotheses hold; the
terminal/empty underlying categories and identity adjunction fit the binders; `n = 0`
does not occur in this statement; and the independent index universe `w` does not
exclude any small set. No characteristic, nonzero, properness, or combinatoriality
assumption is present.

I reran the independent existing-declaration searches. `msearch.py` LeanFinder for
“a left Quillen adjunction descends through a left Bousfield localization when its
derived left functor inverts the localizing arrows” returned only generic derived
functor/localization APIs; the Loogle query `"Bousfield"` returned no hits; and the
Mathlib grep query `Bousfield|Quillen` under `AlgebraicTopology/ModelCategory` found
no model Bousfield descent theorem. Grep of the project and upstream source for
`bousfield_quillen_descent`/`BousfieldQuillenDescent` found no existing declaration.
The categorical `Localization.Bousfield` declarations concern ordinary Hom-set
orthogonality and do not state this model-category result.

The module compiled cleanly with `scompile.py`; its only postponed proof is the
required `sorry`, and the node copy now records the exact theorem signature.
