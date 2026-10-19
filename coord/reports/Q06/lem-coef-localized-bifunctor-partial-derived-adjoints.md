## Worker report

`Sheaf.CategoryTheory.LocalizedBifunctorPartialDerivedAdjoints` states
`HomotopicalAlgebra.ModelInfinity.localizedBifunctorPartialDerivedAdjoints` with one
`sorry`, its theorem proof. All helper definitions contain actual data. The helpers
`leftPartial` and `rightPartial` use the canonical terminal-to-vertex constant map and
product projections. `cofibrantPairLocalizationMap` retains the entire nerve of pairs of
cofibrant objects; `cofibrantPairAtLeft` and `cofibrantPairAtRight` fix an input as
ordinary functors. `NormalizedPartialComparison` packages a coherent equivalence and
its required compatibility with the specified comparison. These are helpers for this
node's comparison, rather than independent notions or replacement dependency modules.

Hypotheses, clause by clause:

- The three ordinary categories are `C`, `D`, `E`, with `Category` and `ModelCategory`
  instances. Completeness and cocompleteness are `HasLimits` and `HasColimits`, as in
  the recorded derived-adjunction dependency. The six
  `HasFunctorialFactorization` instances express both functorial model factorizations
  in each category. Cofibration and initial-object structures come from these model
  categories; no unrelated duplicate structures are supplied.
- The localization targets are `M`, `N`, `P : SSet.{max u v w}`, with
  `SSet.Quasicategory` instances. `qM`, `qN`, `qP` are maps from the enlarged ordinary
  nerves. `hM`, `hN`, `hP : FiniteReedy.IsLocalization ...` assert inversion of weak
  equivalences and the full coherent-functor localization universal property. The
  free universe `w` permits enlargement beyond the categories' universes.
- `F : C ⥤ D ⥤ E` is the ordinary bifunctor, uncurried by Mathlib's
  `Functor.uncurry`. For every cofibrant first input, `hF₁` supplies an ordinary right
  adjoint, preservation of cofibrations, and preservation of trivial cofibrations.
  The last property is preservation of cofibrations and weak equivalences for maps
  satisfying both properties. `hF₂` says the same for `F.flip.obj D₀` at every
  cofibrant second input. No assumption on noncofibrant fixed inputs is imposed.
- `B : M ⨯ N ⟶ P` is the coherent bifunctor. `gamma` is an edge in the internal
  functor simplicial set on the full nerve of
  `CofibrantObject C × CofibrantObject D`, between the localized partial composite
  and `qP` applied to the ordinary bifunctor. `hgamma` requires that edge to be an
  equivalence. Thus arrows and higher simplices are included, not only objects.

Conclusions, clause by clause:

- For each `A : C` with `hA : IsCofibrant A`, the first clause supplies a right
  adjoint `R`, an ordinary adjunction `adj`, functorial replacements `Q`, `e`, `T`,
  `t`, and their cofibrancy/fibrancy and weak-equivalence properties. Its
  `K : ReplacementAdjunction ... qN qP` is the recorded derived adjunction.
  `NormalizedPartialComparison K (leftPartial B (FiniteReedy.object qM A)) ...`
  supplies an equivalence `theta` from the partial to `K.left`.
- For each cofibrant `D₀ : D`, the second clause makes the corresponding assertion
  for `F.flip.obj D₀`, `qM`, and `rightPartial`. The comparison edge is restricted
  using `cofibrantPairAtRight`; the first clause uses `cofibrantPairAtLeft`.
- The extension clause is the `normalization` field of
  `NormalizedPartialComparison`: `a ≫ b ≫ c = d`. Here `Represents` identifies `a`
  with the restriction of `theta`, `b` with the derived replacement comparison
  `K.leftComparison`, `c` with the coherent transformation induced by `L(e)`, and
  `d` with the restriction of the given `gamma`. This equation lies in the homotopy
  category of the entire internal functor category on the cofibrant nerve. It is
  therefore compatibility of coherent transformations, including higher naturality.
  The maps `e` are the specified replacement weak equivalences.
- The final clauses quantify over every vertex `x` of `M` and `y` of `N`, and supply
  `Nonempty (CoherentAdjunction (leftPartial B x) R)` or its right-partial analogue.
  These use the dependency's coherent mapping-space adjunction, not an adjunction
  of homotopy categories. No enrichment or symmetry hypothesis occurs.

Dependency declarations used directly:
`Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction` supplies
`HomotopicalAlgebra.ModelInfinity.ReplacementAdjunction`, `CoherentAdjunction`,
`diagramObject`, and `Represents`, and its theorem
`quillenAdjunctionInfinityLocalization` is the proof's derived-adjunction input.
`Sheaf.CategoryTheory.SystemLocalizationUniversal` supplies
`SSet.coef_system_localization_universal`, the proof's full functor-category descent
input. Their recorded modules are public imports. The proof dependency
`Sheaf.CategoryTheory.CosimplicialFrameMapping` is imported non-publicly; its
`CategoryTheory.frameLargeNerveMap` is also used for nerve maps. The localization
primitives `FiniteReedy.largeNerve`, `object`, `diagram`, `transformation`, and
`IsLocalization` are used from the dependencies' framework. Mathlib's
`CategoryTheory.Functor.Currying` supplies uncurrying and flipping. The dependency
node statements, recorded declarations, full signatures, and docstrings were read.

Edge cases checked: each restriction uses the full subcategory of cofibrant objects,
so noncofibrant inputs are not silently included in a Quillen assumption; no assumption
that every object is cofibrant occurs. The identity replacement gives the ordinary
comparison as the normalization equation. General replacements use the actual
transformation `Functor.whiskerLeft ... (Functor.whiskerRight e L)`. Arbitrary localized
vertices are covered by the last two clauses. Neither input is exchanged using a
symmetry. Constant restrictions and nerve maps include all simplicial degrees. No
extra nonemptiness assumption is introduced (the completeness hypotheses already give
initial and terminal objects). A common universe contains the ordinary categories,
and `max u v w` allows further enlargement for the localization targets.

Searches performed before delivery:

- `msearch.py ... leanfinder "Partial functors of a localized Quillen bifunctor are
  derived left adjoints"`: eight ordinary-category hits, including
  `IsLeftDerivedFunctor` and `Adjunction.localization`/`derived`; no exact coherent
  bifunctor statement.
- `msearch.py ... loogle "CategoryTheory.Localization.lift₂"`: six ordinary
  localization lifting hits; no exact statement.
- `msearch.py ... grep "lift₂|Lifting₂|Quillen" CategoryTheory/Localization`:
  ordinary localization declarations, not this coherent statement.
- `rg` in the upstream `WeilConjectures` tree and shared `lean/Sheaf` for the item id,
  `localizedBifunctorPartialDerivedAdjoints`, `cofibrantPairLocalizationMap`, and
  existing `leftPartial`, `rightPartial`, or `constantAt` definitions: no existing
  statement or helper collision; the item id occurs as a citation in
  `SiftedGoodDiagramCalculus`. Broader searches for `CoherentAdjunction` and
  bifunctors located the dependency interfaces used here.

The cited Higher Algebra PDF was opened at Lemma the project server, pp. 493–494, and
Remark the project server, pp. 119–120. The node's general proof proceeds through its recorded
model-category derived-adjunction dependency; combinatoriality is not added.
No statement correction, new node, dependency-interface repair, or
`STATEMENT-DISPUTED` issue is proposed.

## Worker self-check

This is a worker self-check; the dispatcher explicitly prohibited starting another
agent, and the maintainer performs the independent delivery review. Rereading the
node against the signature found that an initial draft omitted the extension
normalization and redundantly supplied cofibration structures. The delivered version
adds `NormalizedPartialComparison` with the full coherent normalization equation and
uses the model categories' own structures. Its universe `w` also permits arbitrary
further enlargement. Each hypothesis and conclusion is matched above. Only the
named theorem has a postponed proof; helpers use actual constructions.

Validation: `scompile.py Q06 lem-coef-localized-bifunctor-partial-derived-adjoints`
compiled the sandbox and library forms of the delivered module successfully, with
no errors or unexpected warnings. The node copy differs from its shared source only
in `lean`, and all Lean source lines are at most 100 characters.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
