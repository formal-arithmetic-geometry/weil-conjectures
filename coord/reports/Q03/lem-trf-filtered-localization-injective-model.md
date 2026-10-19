## Worker report

The item is stated as `CategoryTheory.filteredLocalization_injectiveModel` in
`Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel`. Its proof is `sorry`.
The original mathematical statement is unchanged. While this worker was running,
the stage-1 split of the item became available; the sandbox node was copied again
from that current split, and the declaration docstring follows all twelve proof
steps and names their dependencies. No stage-1 field is changed.

The statement uses the concrete constructions in the new definition module
`Sheaf.Algebra.Homology.FiniteFilteredLocalization`. The categories use existing
filtered objects, Mathlib's `HomotopyCategory.Plus`, and the explicit category
localization `MorphismProperty.Localization`. No filtered derived category,
comparison functor, graded map, or triangulation is supplied as arbitrary input.
All construction data is real; the named construction-validity theorems have
`sorry` and source/proof docstrings in the new definition node's module.

Hypotheses and clauses of the item, in order:

- An arbitrary abelian category is `(C : Type u) [Category.{v} C] [Abelian C]`.
  Object and morphism universes are independent. `[EnoughInjectives C]` is the
  ordinary extension-property enough-injectives hypothesis. `[HasDerivedCategory.{w} C]`
  chooses the ordinary derived localization used in the final square, with its
  independent morphism universe. Such a choice always exists in a sufficiently
  large universe by `HasDerivedCategory.standard`; no smallness or Grothendieck
  assumption is added.
- `Fil^f(C)` is `FiniteFilteredObjects C none false`. Its objects are the existing
  `FilteredObject C` with `DecreasingFiltration.IsFinite`. Its morphisms are the
  existing `FilteredObject.HomPreservingSteps`. Addition is the underlying
  addition, transferred from the additive subgroup of filtration-preserving maps.
- `K_F^+(C)` is `FiniteFilteredHomotopyPlus C none false`, literally
  `HomotopyCategory.Plus` of that additive category. Cochains are integer-indexed
  and bounded below in the cochain degrees. Chain maps and homotopies are maps
  in the filtered category, so preserve every filtration step. Finite filtration
  bounds may vary with the cochain degree; the stronger globally uniform condition
  is imposed only when an interval is supplied.
- The graded quotient is the existing `DecreasingFiltration.gradedPiece`, namely
  the cokernel of the successive subobject inclusion. `filteredEvaluation ... (some p)`
  uses exactly the existing `FilteredObject.gradedMapSteps` on maps. Mapping this
  additive functor onto complexes gives the quotient complex `F^p/F^(p+1)`;
  kernels and cokernels of complexes are computed degreewise. The recorded
  subquotient module is imported, rather than a second graded-complex definition.
- `finiteFilteredQuasiIso C B` says that every graded image of a homotopy map is
  in `HomotopyCategory.Plus.quasiIso C`. Thus the class being inverted is the
  class in the node, not ordinary underlying quasi-isomorphisms.
  `FiniteFilteredDerivedPlus C B` is the explicit formal localization at this
  class and `finiteFilteredQh C B` is its canonical localization functor.
- Filtered injectivity is precisely the last conjunct of `finiteFilteredProperty`
  with `inj = true`: `∀ p, Injective (K.filtration.gradedPiece p)`.
  `FiniteFilteredObjects C B true` is the full additive subcategory. Its finite
  products and biproducts are justified by finite sums of graded injectives;
  enough injectives is not needed for these additive structures.
- The first conjunct quantifies over every `K : CochainComplex.Plus ... false`.
  It produces `I : CochainComplex.Plus ... true` and an actual chain map `f` into
  its image under inclusion, whose homotopy class lies in `finiteFilteredQuasiIso`.
  Thus this is an actual filtered quasi-isomorphism to a bounded-below termwise
  filtered-injective complex, not just an isomorphism after localization.
- The second conjunct quantifies over every pair `K I` of bounded-below filtered
  homotopy objects. Its only extra premise is exactly termwise graded injectivity
  of `I`. `Function.Bijective ((finiteFilteredQh C B).map : (K ⟶ I) → _)`
  is the localization-induced Hom bijection in the node.
- The third conjunct is `IsEquivalence` of `filteredInjectiveComparison C B`,
  which is definitionally inclusion on bounded-below homotopy categories followed
  by the actual localization. This gives full faithfulness and essential
  surjectivity of the specified functor. The fourth conjunct is its `IsTriangulated`
  for the standard cone triangulation and the induced localization triangulation.
  The shift comparison is the composite of the standard inclusion and localization
  comparisons; no triangulated structure is selected arbitrarily.
- The fifth conjunct states `Injective` for every degree of every representative
  and every `filteredEvaluation ... p`. `p = none` is forgetting; `p = some r` is
  grading at every integer `r`. The resulting complexes are bounded below because
  these are additive functors on `HomotopyCategory.Plus`.
- The sixth conjunct gives the comparison squares as natural isomorphisms of
  the specific functor composites. The left composite is the canonical comparison
  followed by the localization-defined `finiteFilteredDerivedEvaluation`; the
  right composite is termwise forgetting/grading of the injective representative
  followed by `DerivedCategory.Plus.Qh`. These are exactly the two squares in
  Stacks 015Q, with their bottom row written through `K^+(C)`. The fifth conjunct
  shows that this row factors through ordinary injective complexes.
- The theorem is parameterized by `B : Option (ℤ × ℤ)`. `none` gives the whole
  assertion. `some (a,b)` enforces `F^a = ⊤` and `F^(b+1) = ⊥` on every object
  of both categories, so the produced resolutions retain the same interval and
  every assertion, equivalence and comparison is in that interval. In particular
  all intervals `a ≤ b` requested in the item are included.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`, with its full
  signature and normal-mono/epi and finite-product requirements.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective`,
  `EnoughInjectives`; `InjectiveResolution` was also read in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`. The item needs
  injective objects and enough injectives, not a second ordinary resolution type.
- `WeilConjectures.CategoryTheory.PBCFiltration`: read the currently recorded
  `PBCDecreasingFiltration`, `PBCFilteredObject` and its category, `IsFinite` and
  `gradedPiece` through `scompile.py --source`. Its representation differs from
  the recorded subquotient consumer. The lean-only dependency repair below uses
  the already published equivalent representation, without a new filtration.
- `Sheaf.CategoryTheory.Filtration`, reexporting
  `WeilConjectures.CategoryTheory.Abelian.Filtration` and
  `WeilConjectures.CategoryTheory.Filtration`: `DecreasingFiltration`,
  `FilteredObject`, `FilteredObject.HomPreservingSteps`, `IsFinite`, `gradedPiece`.
  These source declarations and their docstrings were read in full.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`:
  `DecreasingFiltration.complexStep`, `complexQuotient`, `complexQuotientπ`,
  `complexCycleRepresentatives`, `complexCycles`, `complexBoundaries`, read in full.
- `Sheaf.CategoryTheory.FiniteFiltrationInduction`:
  `FilteredObject.restrictionSteps`, `exists_gradedMap_steps`, `gradedMapSteps`.
  The unique cokernel-map API is reused for the graded functor.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`/`.Plus`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Plus`, `DerivedCategory.Plus.Qh`.
  The bounded-below homotopy, localization, and triangulation APIs were read in
  `HomotopyCategory.Plus`, `Localization.Triangulated`, and
  `Triangulated.Subcategory` as well.
- Stated proof dependencies are imported privately in the item module:
  `Sheaf.CategoryTheory.DoubleComplexTotal`,
  `Sheaf.Algebra.Homology.FirstQuadrantAugmentation`,
  `Mathlib.Algebra.Homology.HomologySequence`, and `.HomologySequenceLemmas`.
  The three new stage-1 filtered proof lemmas currently have no Lean module,
  so have no import to add; their names and uses are retained in the proof docstring.

Edge cases checked mathematically before writing:

- Zero object/complex: all graded objects are zero and injective; zero resolutions
  work in every filtration interval, and the additive categories have empty sums.
- One-step interval `a = b`: this is the ordinary bounded-below injective model
  placed in filtration degree `a`, not only degree zero.
- Arbitrary positive or negative cochain lower bound: `CochainComplex.Plus` uses an
  existential integer lower bound, not a natural-indexed complex starting at zero.
- Filtration bounds varying without bound across cochain degrees are allowed for
  `B = none`. Each first-quadrant total degree is a finite sum, so remains finite
  filtered. A supplied interval is retained by every term and every finite sum.
- A graded piece outside a fixed interval is zero; forgetting still recovers the
  entire underlying injective object by finite splitting. `some (a,b)` with
  `b < a` just gives the zero filtered category and does not exclude any requested
  interval; all assertions hold there too.
- Object, Hom, and ordinary derived Hom universes remain independent. Localizations
  are taken in their canonical sufficiently large universe, as the source permits.

Searches (all performed before adding the construction):

1. `msearch.py ... leanfinder` with “homotopy category of bounded below finite
   filtered injective complexes equivalent to filtered derived localization”:
   eight ordinary localization/derived functor hits, no filtered-injective model.
2. `msearch.py ... loogle` with `"IsKInjective", "Qh"`: ordinary
   `CochainComplex.IsKInjective.Qh_map_bijective` and
   `DerivedCategory.Plus.Qh_map_bijective_of_isKInjective`; neither applies to
   the finite filtered exact category or defines graded quasi-isomorphisms.
3. `msearch.py ... grep` with
   `Filtered.*Injective|filtered.*localization|filtered.*quasi` in `Algebra/Homology`:
   zero hits.
4. `msearch.py ... leansearch` with “additive category of finite decreasing
   filtered objects and filtered derived localization at graded quasi
   isomorphisms”: eight ordinary derived-category/localization hits, no match.
5. `rg` through Mathlib CategoryTheory, WeilConjectures and lean/Sheaf for
   `FilteredObject.*Preadditive`, `preadditive.*FilteredObject`,
   `FiniteFilteredObject`, `finiteFilteredLocalization`, `FilteredInjective`:
   no generic additive filtered-object/localization construction.
6. DAG search and `tools/blueprint_refs.py search 'filtered homotopy'`: the latter
   returned `prop-trf-trace-formal-laws`; the cone-localization theorem is the
   triangulation assertion, not a definition module. Existing
   `def-kun-finite-filtered-module-homotopy` is restricted to modules with a
   uniform finite filtration and `def-trf-two-step-filtered-module-derived` to
   two-step module filtrations; neither represents arbitrary abelian categories
   with degreewise finite filtrations. Their full modules were inspected.
7. Source search for the item id in WeilConjectures: no declaration of this lemma.

No statement dispute or mathematical correction was needed. Both delivered files
compile separately in dependency order through `scompile.py`, without errors or
warnings. The wrapper also compiled their library forms in its private overlay.

## New nodes

`def-trf-finite-filtered-localization` defines the missing generic additive
categories of finite filtered objects and filtered injectives, their bounded-below
homotopy categories, graded quasi-isomorphisms, explicit localization, canonical
comparison and forgetting/grading functors. It includes their construction-validity
laws: finite products, graded-map functor laws, additivity, calculus of fractions,
triangulation compatibility and inversion by ordinary derived evaluation. These
are the properties needed to define the canonical structures, not arbitrary input
interfaces. The source is Stacks 0121, 05S2, 05TW and 015Q; all construction-validity
theorems have detailed source/proof docstrings and are listed in `lean.declarations`.
The searches above are stored verbatim from `searches.jsonl` in this new node's
`mathlib_searches`, together with the direct DAG/source search. No existing generic
definition node or declaration supplies these constructions. The node cites the
existing filtration, subquotient, graded-map, injectivity, derived-category and
triangulated-category nodes; the item gains only this new statement dependency.

## Dependency modules

`def-sp-filtration` receives only a lean-record repair under §1(B), using
`existing: true`, so no extra module is written. Its currently recorded
`PBCDecreasingFiltration` is mathematically the same decreasing-subobject notion,
but the recorded `def-sp-filtered-complex-subquotients` and canonical
`FilteredObject.gradedMapSteps` consume upstream `DecreasingFiltration`, not that
PBC structure. The repaired record refers to the existing
`Sheaf.CategoryTheory.Filtration` interface, which exposes exactly that upstream
type and its already published category, finite predicate, and graded quotients.
It preserves arbitrary integer filtration bounds and all clauses of the node.
The delivery contains no second definition and changes no dependency statement.
The existing declaration probe of the dry run checks every recorded name.

## Second reading by Q03

I read the item node, its Stacks source (Derived Categories, Tags 05TW, 05TY,
and 015Q), the new definition node, and every recorded dependency declaration.
The statement is rendered by
`CategoryTheory.filteredLocalization_injectiveModel` in
`Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel`.

The node's clauses match the Lean signature in order:

1. `C : Type u` with `[Category.{v} C]`, `[Abelian C]`, `[EnoughInjectives C]`,
   and `[HasDerivedCategory.{w} C]` is the abelian category and the chosen
   ordinary derived localization. `FiniteFilteredObjects C B false` is
   `Fil^f(C)` (with optional fixed bounds).
2. `FiniteFilteredHomotopyPlus C B false` is the bounded-below filtered
   homotopy category, with filtration-preserving maps and homotopies;
   `filteredEvaluation ... (some p)` is the canonical graded quotient.
3. `finiteFilteredQuasiIso C B` inverts exactly maps whose every graded map is
   a quasi-isomorphism, and `finiteFilteredQh C B` is the resulting localization.
4. The first conjunct supplies a bounded-below termwise filtered-injective
   representative and an actual filtered quasi-isomorphism. The second conjunct
   gives the localization Hom bijection for every bounded-below `K` and every
   termwise graded-injective `I` (the premise is exactly the node's “such I”).
5. The third and fourth conjuncts state that the canonical inclusion followed by
   localization is an equivalence and is triangulated, respectively.
6. The fifth conjunct states that forgetting and every graded evaluation of an
   injective representative is a complex of ordinary injectives. The sixth gives
   the natural comparison isomorphisms with the ordinary bounded-below derived
   category functor, for forgetting (`none`) and every graded piece (`some p`).
7. `B : Option (ℤ × ℤ)` implements the unrestricted case and every fixed finite
   interval; the interval equations are in `finiteFilteredProperty` and are
   retained by all constructions.

The hypotheses agree with the source and the node. The independent ordinary
derived-category instance is required to type the two comparison functors and is
the chosen localization referred to by `def-weil-abstract-derived-category`; no
Noetherian, Grothendieck, smallness, or uniform filtration hypothesis was added.
The source's strict-monomorphism strengthening in Tag 05TW is not part of this
node's stated conclusion, so the Lean theorem correctly does not add it.

Edge cases checked were the zero object and zero complex, empty finite sums,
arbitrary positive or negative lower cochain bounds, one-step intervals `a = b`,
graded indices outside a fixed interval, and `B = none`. Bounds may vary with
cochain degree in the unrestricted case, while `some (a,b)` enforces the same
interval in every term. The independent object, morphism, and derived Hom
universes remain unconstrained.

I repeated the Mathlib, upstream, project, and DAG searches recorded above with
`msearch.py`, `rg`, and the source declaration search. There is no existing
generic filtered-injective localization theorem or construction. The new
`def-trf-finite-filtered-localization` node is therefore required. I also checked
its declarations and docstrings: all data is constructive, while only named
construction-validity propositions are postponed.

One dependency interface was unusable as recorded: `def-sp-filtration` pointed
to the upstream `PBCDecreasingFiltration`, while the recorded filtered-object,
graded-map, and subquotient declarations consume `DecreasingFiltration`. I
repaired only that dependency's `lean` record to the existing
`Sheaf.CategoryTheory.Filtration` interface, preserving the dependency statement
and all of its arbitrary-integer filtration clauses. No item statement or target
unit was changed. Both modules compile cleanly with `scompile.py`, including the
private overlay and library forms.
