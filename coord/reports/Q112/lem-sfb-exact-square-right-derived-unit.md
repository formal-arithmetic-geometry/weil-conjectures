## Worker report

The module `Sheaf.CategoryTheory.ExactSquareRightDerivedUnit` states
`CategoryTheory.Functor.exactSquare_rightDerived_unit`, with `sorry` as its entire proof.
It also defines `CategoryTheory.Functor.exactSquareRightDerivedPostcompositionUnit` by
composing the canonical homotopy-composition and exact-localization identifications
with the recorded derived unit. This helper has real data and belongs to the notion
of the item's specified unit; it is not a new independent notion. No dependency repair,
new node, or statement correction is needed. Only the item's `lean` record changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The four abelian categories are `A`, `A'`, `B`, `B'`, their explicitly bound
  `Category` instances, and the four `Abelian` instances. Each category has independent
  object, morphism, and localization universes (`uA`, `vA`, `wA`, etc.).
- Their ordinary unbounded derived categories are `DerivedCategory A`, etc., using
  `[HasDerivedCategory.{wA} A]`, etc. Their homotopy localizations are
  `DerivedCategory.Qh` and the complex-to-homotopy quotient is
  `HomotopyCategory.quotient A (.up ℤ)`. Thus `Qh.obj (quotient.obj P)` is exactly the
  node's `QP`, in its stipulated homotopy-category convention; no boundedness is imposed.
- The resolution hypotheses are `hA` and `hA'`: for every `CochainComplex ... ℤ`
  there exist `I` and `s : P ⟶ I` with `I.IsKInjective ∧ QuasiIso s`. In particular
  no monomorphism is required. Mathlib's `IsKInjective` says every map from an acyclic
  complex is homotopic to zero, exactly as the node requires.
- The horizontal functors are `F : A ⥤ B` and `G : A' ⥤ B'`, with only their
  `Additive` instances. No left-exactness hypothesis is added to them.
- The vertical functors are `U : A ⥤ A'`, `V : B ⥤ B'`, additive and preserving
  finite limits and finite colimits. This is precisely exactness for these abelian
  categories. Their descents are the recorded Mathlib `mapDerivedCategory` functors.
- The ordinary natural isomorphism `c : F ⋙ V ≅ U ⋙ G` renders `VF ≅ GU`, because
  Lean's `⋙` lists the functor applied first on the left.
- `F.rightDerivedFunctorOfQuasiIsoResolutions hA` and
  `G.rightDerivedFunctorOfQuasiIsoResolutions hA'`, with their recorded units, are
  the total right-derived pairs specified by `def-sfb-right-derived-functor`.
  The definition there fixes a representative of the universal pair; it does not
  add a new assumption on this item.
- The first conjunct is `IsRightDerivedFunctor` for
  `F.rightDerivedFunctorOfQuasiIsoResolutions hA ⋙ V.mapDerivedCategory`, the displayed
  postcomposition unit, and `HomotopyCategory.quasiIso A (.up ℤ)`. Mathlib defines
  this as the left Kan extension along the localization `Qh`, hence exactly the
  total right-derived universal property for `QVF` in the node.
- The helper's domain is `(F ⋙ V).mapHomotopyCategory (.up ℤ) ⋙ Qh`. Its formula
  first splits this degreewise composite with `mapHomotopyCategoryCompIso.inv`,
  then uses `V.mapDerivedCategoryFactorsh.inv` to pass from `Qh V_K` to `D(V) Qh`,
  and finally applies `whiskerRight` of the recorded unit by `D(V)`. Associators
  only identify the parenthesizations. Its component is precisely `D(V)(ηF_P)`
  under the node's canonical identifications.
- The second conjunct is `∃! γ` from `RF ⋙ D(V)` to `D(U) ⋙ RG`. The property is
  quantified over every complex `P`, including complexes that are not K-injective.
  The left side is the postcomposition unit followed by `γ.app (Qh.obj (quotient.obj P))`.
  Lean composition `≫` reads in the reverse order of the node's usual composition
  notation, so this is exactly `γ_QP D(V)(ηF_P)`.
- On the right, `Qh.map ((NatTrans.mapHomotopyCategory c.hom ...).app ...)` is
  `Q(c_P)`. The next composition comparison identifies `(UG)_K P` with `G_K(U_K P)`.
  The recorded `G` unit is then evaluated at `U_K P`. Finally `RG.map` of
  `U.mapDerivedCategoryFactorsh.inv.app ...` identifies `RG(Qh(U_K P))` with
  `RG(D(U)(Qh P))`. These are exactly `ηG_UP Q(c_P)` with the stipulated canonical
  localization identifications.
- There is no K-injective-preservation assumption on `U` and no `IsIso γ` conclusion.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Qh`, and `DerivedCategory.quotientCompQhIso` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-sp-left-exact-additive`: `CategoryTheory.Functor.Additive` in
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`; its recorded match explicitly
  lists this clause. Its ordinary higher-derived functors are not being used here.
- `lem-weil-pbc-exact-functor-derived-factorization`:
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactorsh` in
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. The full signatures allow
  independent object, morphism, and localization universes at both ends.
- `def-sfb-right-derived-functor`: all six recorded declarations were read in
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, especially
  `rightDerivedFunctorOfQuasiIsoResolutions`, its `Unit`, `_universal`, and
  `rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso`. That module is publicly imported.
- Proof dependencies: `CategoryTheory.Localization.essSurj` in
  `Mathlib.CategoryTheory.Localization.Predicate` and
  `CochainComplex.IsKInjective.Qh_map_bijective` in
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`, both imported as proof imports.
  The other two proof dependencies are already statement imports.
- The standard total-derived predicate is
  `CategoryTheory.Functor.IsRightDerivedFunctor` in
  `Mathlib.CategoryTheory.Functor.Derived.RightDerived`. Its definition was read;
  it introduces no preservation-of-injectives assumption.

Source check: read `literature/stacks-project/derived.tex`, the definition of
K-injectivity, lemma-K-injective (Tag 070I), lemma-K-injective-defined (Tag 070Y),
and lemma-enough-K-injectives-implies. Read the source-library
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`,
including `rightDerivedFunctorPlusBaseChangeAux` and its unit factorization. This is
a bounded-below analogue, not a declaration of the present unbounded assertion.
The theorem docstring gives all six proof steps of the item: invertibility on
K-injectives, chosen representatives and Hom lifts, construction/naturality of β,
factorization on arbitrary complexes, uniqueness, and specialization to the square.

Edge cases checked before writing: identity vertical functors and identity square;
zero `F` or zero exact `V`; the zero complex; arbitrary unbounded complexes; a
K-injective input; and a vertical functor `U` which does not preserve K-injectives.
The unit equation remains well typed in all cases. Universality uses K-injective
targets in `A` alone; the `G` pair uses the separate `A'` resolution hypothesis.
No argument requires extra injectivity, boundedness, nonzero objects, or equal
universes. No statement dispute or node fault was found.

Searches, all made before the new declarations:

- `msearch.py ... leanfinder`, query: "Postcomposition of a total right derived
  functor by an exact functor and unique unit compatible comparison in an exact
  square". Eight hits, headed by `LocalizerMorphism.rightDerivedFunctorComparison`
  and its factorization lemmas. They construct a comparison from an already
  available universal pair; they do not assert the needed postcomposition property.
- `msearch.py ... loogle`, query: `"IsRightDerivedFunctor", "comp"`. Twelve hits,
  including a postcomposition instance requiring a left adjoint, shifts, and
  generic composition comparisons. No exact match; the left-adjoint hypothesis
  is absent from the node and that instance is not in pinned `RightDerived.lean`.
- `msearch.py ... grep`, query:
  `rightDerived.*[Pp]ostcomp|isRightDerivedFunctor.*[Cc]omp|rightDerivedFunctorComparison_fac`.
  Four factorization hits in `PointwiseRightDerived.lean`; none proves the conjunction.
- `msearch.py ... leansearch`, query: "total right derived functor postcomposition
  exact functor K injective resolutions universal property". Eight hits including
  `totalRightDerived` and its predicate, and ordinary `rightDerived`; no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, by item id and patterns
  `TotalRightDerived|totalRightDerived|KInjective|HasKInjective|rightDerivedUnit`,
  `exactSquare|exact_square`, and postcomposition/comparison/base-change names.
  The exact-square modules require all functors exact or concern the bounded-below
  setting; `ExactPostcompositionKInjectiveDescent` states normalized descent for
  an adjoint with an exact composite, a different result. No existing declaration
  states this item. The literal item id has no existing Lean occurrence.

Validation: `scompile.py Q112 lem-sfb-exact-square-right-derived-unit .../ExactSquareRightDerivedUnit.lean`
passed the sandbox and library-mode compiles (2.2 seconds and 2.1 seconds) with no
errors or unexpected warnings. `autoImplicit` is explicitly disabled.

## Second reading by Q112

This is the author's separate second reading; the dispatcher's instructions prohibit
starting another agent, and the maintainer supplies the independent review.
Reopened the node and complete module and checked each binder and both conjuncts.
The four independent category/derived-category sizes, the arbitrary-quasi-isomorphism
resolution hypotheses, additive horizontal functors, exact vertical functors, and
orientation `F ⋙ V ≅ U ⋙ G` agree with the node. The first conjunct proves
universality rather than assuming it. The second supplies existence and uniqueness,
and its equation applies to every complex. Traced each factor's source and target:
the inverse factor for `V` belongs in the unit, while the inverse factor for `U`
belongs after the `G` unit on the equation's right side. Both orientations are
correct. The homotopy composition comparison for `U ⋙ G` must also be inverted,
as written. The use of `Qh (quotient P)` is the stipulated `QP`, with the standard
`quotientCompQhIso` supplying the identification with complex localization. The
uniqueness is for the whole natural transformation, not just a selected component.
The helper introduces no arbitrary map or existential choice. No mismatch was
found and no statement correction was made. All postponed proof content is confined
to the one named theorem matching this DAG node.
