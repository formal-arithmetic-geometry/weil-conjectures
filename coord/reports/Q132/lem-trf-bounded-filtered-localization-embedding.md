## Worker report

The item is stated, with `sorry`, as
`CategoryTheory.boundedFilteredLocalizationEmbedding_fullyFaithful_exact` in
`Sheaf.Algebra.Homology.BoundedFilteredLocalizationEmbedding`.
The functor is constructed by localizing the actual full inclusion of bounded
uniformly filtered homotopy categories. Its shift comparison is the comparison
induced by that inclusion and localization, not an arbitrary shift isomorphism.
No mathematical assertion is proved in this delivery.

Clause-by-clause reading of the unchanged item:

- An arbitrary abelian category is `(C : Type u) [Category.{v} C] [Abelian C]`.
  Object and morphism universes remain independent; no enough-injectives hypothesis
  and no chosen ordinary derived category is needed.
- Decreasing filtrations and filtered maps are the recorded upstream
  `DecreasingFiltration`/`FilteredObject`, as exposed by the existing
  `FiniteFilteredObjects C B false`. A complex in that additive category is
  exactly a complex with filtration-preserving differentials. Its homotopy
  category uses homotopies with filtered components.
- `uniformFilteredHomotopyProperty` requires `∃ a b : ℤ, a ≤ b ∧ ∀ n : ℤ, ...`.
  Its two equalities are `(K.obj.as.X n).obj.filtration.step a = ⊤` and the
  analogous equality at `b+1` with `⊥`. These are uniform bounds in cochain
  degree, as required, rather than merely termwise finite filtrations.
- `FiniteFilteredHomotopyPlus` supplies the lower cochain bound. The extra
  Boolean `bounded = true` supplies `∃ d, ∀ n, d < n → IsZero ...` for the
  underlying degree object. Thus `UniformFiniteFilteredHomotopy C B true` is
  the bounded category, and the version with `false` is bounded below.
  The full subcategories retain exactly the ambient filtered maps and homotopies.
- The existing `finiteFilteredQuasiIso` tests every graded map with
  `∀ p : ℤ, HomotopyCategory.Plus.quasiIso C (...)`.
  `uniformFilteredHomotopyQuasiIso` is its inverse image along the full inclusion.
  It does not replace graded quasi-isomorphisms by ordinary quasi-isomorphisms.
- `UniformFiniteFilteredHomotopyLocalization` is precisely that morphism
  property's formal `Localization`, with the standard inherited localization
  triangulation. The helper's proof prerequisites are named theorems and
  explicit clauses of its new DAG definition, explained below.
- `boundedFilteredHomotopyInclusion` forgets only the upper cochain bound.
  `boundedFilteredHomotopyLocalizer` has this functor and the definitionally
  identical graded-map test as its preservation proof.
  `boundedFilteredLocalizationEmbedding` is this localizer's
  `localizedFunctor` at the two canonical localization functors `Q`.
- Full faithfulness is `Nonempty (...).FullyFaithful`. Exactness is rendered by
  `(...).Additive` and `(...).IsTriangulated`, using the separately constructed
  canonical `CommShift ℤ` instance. The inclusion's shift comparison is inherited
  by `ObjectProperty.lift`; localization descends that very comparison.
- `B = none` permits filtration intervals depending on the complex.
  `B = some (a,b)` fixes the existing category of flags in this interval, on
  objects, chain maps and homotopies. The theorem's `_hB` requires `a ≤ b`
  whenever an interval is prescribed. For `none` this condition is empty;
  for every actual interval `[a,b]` it is exactly the node's interval condition.
  One theorem thus covers both clauses with the same canonical construction.

Dependency declarations inspected and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`. Its finite-products/normal-mono/normal-epi
  definition is the recorded equivalent form; zero and biproducts are derived.
- `def-sp-filtration`: `CategoryTheory.DecreasingFiltration`,
  `WeilConjectures.CategoryTheory.Abelian.Filtration`. I read its current source
  through `scompile.py --source`, because the older checkout lacks that file.
  The fields are `F` and `F_succ_le`, and `gr` is the successive cokernel.
  `Sheaf.CategoryTheory.Filtration` supplies the `step` compatibility accessor,
  the existing filtered-map category and `gradedPiece` alias.
- `def-sp-filtered-complex-subquotients`:
  `Sheaf.Algebra.Homology.FilteredComplexSubquotients`, particularly
  `DecreasingFiltration.complexStep`, `complexQuotient`, `complexQuotientπ`
  and `complexCycles`. I read all signatures and docstrings. The graded
  complexes are the same successive cokernels; no second graded construction
  is supplied here. This module is publicly imported through the existing
  `FiniteFilteredLocalization` module.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, and the corresponding
  ordinary complex and quasi-isomorphism API used by graded evaluation.
  Our localization uses graded tests, so it does not substitute `DerivedCategory`
  of the nonabelian category of flags for the filtered localization.
- `def-weil-triangulated-category`: the recorded Mathlib interfaces
  `Pretriangulated`, `IsTriangulated`, and `Functor.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`, `.Functor`.
  I read the class signatures (TR1--3, TR4 and preservation of distinguished triangles).
- New definition dependency `def-trf-uniform-filtered-homotopy-localization`:
  `Sheaf.Algebra.Homology.UniformFilteredHomotopyLocalization`, all declarations
  recorded in its `lean.declarations`. It reuses
  `FiniteFilteredHomotopyPlus`, `FiniteFilteredObjects`, `finiteFilteredQuasiIso`
  and their graded evaluation from `Sheaf.Algebra.Homology.FiniteFilteredLocalization`
  (`def-trf-finite-filtered-localization`).

The proof modules `Sheaf.Algebra.Homology.FilteredConeLocalization` and
`Sheaf.Algebra.Homology.FilteredBoundedLocalizationComparison` are imported
non-publicly. Their recorded declarations are `filteredConeLocalization` and
`uniformFiltered_bounded_localization_comparison`. The latter gives canonical
upper truncation with its induced filtration and the comparison of chain
localizations. Its source explains the cylinder passage between chain and
homotopy localizations. The remaining proof dependencies are Mathlib leaves:
`ObjectProperty.IsTriangulated` and its cone-class instances in
`Mathlib.CategoryTheory.Triangulated.Subcategory`; localization triangulations
and `Functor.distTriang_iff` in `Mathlib.CategoryTheory.Localization.Triangulated`;
`Localization.lift`, `liftNatTrans`, `liftNatIso` in `.Localization.Predicate`;
`Localization.exists_rightFraction` and `MorphismProperty.RightFraction.map_eq_iff`
in `.Localization.CalculusOfFractions`. These modules are available through
the imports of the two proof modules and the helper. No unstated project proof
dependency is silently used as a premise.

The main theorem's docstring carries all six proof steps: inherited cone
triangulations, graded-acyclic cone systems, localized inclusion, truncation of
roofs for fullness, truncation of common refinements for faithfulness, and
shift/additivity/distinguished-triangle compatibility for exactness. Every step
retains fixed filtration intervals. The three helper `sorry`s have their own
source and complete proof docstrings and are explicit prerequisites in the
new definition node's statement: closure under the cone triangulation,
left fractions and compatibility with triangulation. All definitions and
instance constructions have actual data, with no `sorry` in a definition.

Edge cases checked mathematically: the zero complex and the zero category;
one-step filtration `a=b`; zero objects with any assigned interval; shifts by
positive, zero and negative integers; source and target with different finite
intervals when `B=none` (their cone uses min/max); an arbitrary negative upper
or lower cochain bound. Bounds are existential integers, with no fixed finite
cochain interval imposed on the whole category. Lower-boundedness permits
unbounded positive support. The unrestricted case does not impose a uniform
interval across all objects. There are no test-index universe restrictions.
`ObjectProperty.IsTriangulated` explicitly permits closure up to isomorphism,
so the chosen representatives need not be closed literally under homotopy
isomorphisms. This matches the node's proof and Mathlib's intended API.

Searches: `msearch.py leanfinder` with the full bounded filtered localization
comparison returned ordinary derived-category, homological functor and shape
support results, not this filtered comparison. `loogle` with
`CategoryTheory.Functor.FullyFaithful, Localization` returned no hits; a later
`"HomotopyCategory", "Localization"` query returned ordinary homotopy/derived
localization declarations, which do not give the graded filtered assertion.
`msearch.py grep` for `FilteredDerived|filtered.*localization|FilteredComplex`
in Algebra/Homology returned no hits. `leansearch` for uniform finite filtered
homotopy localizations returned ordinary `DerivedCategory`, the general
homotopy category, and generic triangulated localization instances.
The exact tool outputs are retained in the new definition node's search records.
Local `rg` in Mathlib, WeilConjectures, and `lean/Sheaf` found no existing
`boundedFilteredLocalizationEmbedding` or uniform filtered homotopy restriction.
The item-id source grep found no existing assertion to reuse. The project's
newly landed uniformly filtered CHAIN localizations and the older termwise
finite filtered homotopy model were both read and distinguished by their full
definitions, not by names. `dag/lean_names_upstream.json` has no name collision.

Validation: both delivered files compiled separately in dependency order through
`scompile.py`, including the private overlay and library checks, with no errors
or warnings. All compilation used the wrapper and its default 60-second per-file
limit. Dry-run and delivery results are recorded by the delivery wrapper.
No statement correction, disputed statement or dependency-record repair.

## New nodes

`def-trf-uniform-filtered-homotopy-localization` supplies the missing adapter
between the existing termwise-finite filtered homotopy category and the uniformly
finite filtered homotopy categories required by this item. It restricts the
existing homotopy category by degree-independent filtration bounds and the
optional upper cochain bound, restricts its existing graded quasi-isomorphisms,
and uses Mathlib's inherited full-subcategory triangulation and its standard
localization. Source: Stacks 05S2 and 05S6, with closure and cone-system
constructions 05RQ and 05RG, restricted to the uniform/fixed-interval case.
The three prerequisite assertions are the named proof obligations needed to
construct these structures. Their natural-language proofs are in their own
docstrings; the actual object and map definitions are not chosen from a mere
existence assertion. The record lists every declaration in the module.

I searched the DAG with `rg` and `blueprint_refs.py search 'filtered homotopy'`
(the latter returned only `prop-trf-trace-formal-laws`), Mathlib with LeanSearch,
LeanFinder, Loogle and grep, and both project source trees. Existing
`def-trf-finite-filtered-localization` permits per-term finite bounds when no
interval is prescribed. Existing `def-trf-uniform-finite-filtered-localization`
uses filtrations of entire complexes and localizes CHAIN maps; it supplies
neither this homotopy full-subcategory restriction nor its inherited
triangulation interface. The new node is this model/transport construction;
it reuses the former category and its maps verbatim and does not redefine
filtrations, graded maps, homotopy, or the formal localization construction.
The source also identifies these chain and homotopy localizations by the
filtered cylinder argument (step 4 of the recorded comparison proof).

## Second reading by Q132

No second reading by a worker: the dispatched brief prohibits starting other
agents; the maintainer's independent review reads the delivery.
