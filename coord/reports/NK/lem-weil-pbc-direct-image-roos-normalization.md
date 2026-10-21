## Worker report

The module `Sheaf.CategoryTheory.DirectImageRoosNormalization` states
`CategoryTheory.directImageRoosNormalization`. Its only postponed theorem is
this item, with proof `sorry` and the complete DAG proof plan in its docstring.
The item's statement, statement dependencies and proof dependencies are unchanged.
No new nodes or dependency modules are needed.

The six helper declarations belong to the normalization introduced by this item.
`LimitData` and `DirectImageData` package choices of the existing dependency
interfaces; they define no new derived categories, inverse limits, direct images
or evaluations. `RoosTriangleData` records exactly the specified cone transport.
`ordinaryInclusion`, `alpha` and `productMap` have actual data built from the
existing Roos, product and evaluation constructions. No definition uses `sorry`
or chooses an object from an existence theorem with undetermined data.

Hypothesis-by-hypothesis correspondence:

- Small presented sites: `C D : Type u`, `[SmallCategory C]`,
  `[SmallCategory D]`, and the topologies `J K`.
- Ring sheaves: `R : Sheaf J RingCat.{u}` and `S : Sheaf K RingCat.{u}`.
  No extra commutativity assumption is imposed.
- Ringed geometric morphism: `f : RingedToposMorphism R S`, using its actual
  induced module direct image `f.modules`.
- Specified inverse-image ring isomorphism: `_ringIso : IsIso f.ringMap`.
  Its inverse is uniquely determined by the structural map. This requires that
  very map to be invertible, not merely an unrelated isomorphism of objects.
- Exact module pullback and adjunction: the additive functor `F`,
  `_adj : F ⊣ f.modules`, `[PreservesFiniteLimits F]` and
  `[PreservesFiniteColimits F]`. Its fixed right adjoint determines module
  pullback uniquely up to adjunction isomorphism; no arbitrary map is substituted.
- Unbounded derived categories and size: the four `[HasDerivedCategory.{w} ...]`
  binders. Complexes are indexed by all integers. Towers are literally
  `ℕᵒᵖ ⥤ ...`; the paper's positive level is `n + 1`.
- Exact countable products on both module categories:
  `[HasExactLimitsOfShape (Discrete ℕ) ...]` for `R` and `S`.
- The two derived `HasCountableProducts` binders supply chosen products for
  `∏ᶜ`. Their existence is the recorded K-injective product and strict-tower
  homotopy-limit interfaces. They are the paper's derived products; they do not
  impose product exactness on the derived categories.
- The instruction to use the existing total derived functors and normalized
  comparison is unpacked by `d : DirectImageData f.modules`. The four
  `IsRightDerivedFunctor` fields and K-injective unit-invertibility properties
  are precisely the dependency's choices. The theorem quantifies over all such
  choices. There is no additional acyclicity or boundedness assumption.
  `ordinary_components` specifies the ordinary comparison by its limit legs.
  `comparison_unit` fixes `a` by the common-underived-composite normalization.
  `evaluationIso` and `evaluation_unit` are the dependency's identifications
  with levelwise derived direct image, retaining the transitions. They do not
  identify strict derived towers with arbitrary towers in the derived category.

Clause-by-clause correspondence:

- `alpha d M` is Mathlib's `piComparison d.direct ...`, whose components are
  exactly `d.direct.map (Pi.π _ n)`. `IsIso (alpha d M)` asserts invertibility.
  `productMap d M` identifies its target with the product of the actual levels
  of `d.tower.obj M`, using `Pi.map` of the inverse evaluation identification.
- The first equation for each `M` says this comparison commutes with `s`,
  using the existing `towerProductShift` on both sides.
- The equation involving `towerTransitionEndomorphism` says it commutes with
  `1-s`, and is the middle square of the asserted triangle morphism.
- `T : RoosTriangleData d.source` and `U : RoosTriangleData d.target` provide
  the canonical triangles. `distinguished` uses the dependency's
  `IsDerivedLimitTriangle` with total derived inverse limit as first vertex.
- The actual cone vertex is the existing `roosF.obj X = Cone(roosU X)[-1]`.
  `projection_model` uses the existing `roosProj`, with coordinate `x`.
  `boundary_model` uses exactly the last map of
  `CochainComplex.mappingCocone.triangle (roosU X)` followed by the canonical
  localization/shift comparison. In the node's coordinates, `b(z) = (z,0)`.
- `productComparison` identifies the termwise product with the derived product;
  `product_components` fixes each leg as `Q(π_n)` followed by the specified
  evaluation identification. Thus this is not an arbitrary product isomorphism.
- `coneComparison` is natural on every representing complex. `normalization`
  says `Q(ordinaryInclusion X) ≫ coneComparison_X = η_X`. The inclusion is
  `roosLift` of the actual ordinary limit legs, with the already proved
  `ExactProductsRoos.inclusion_difference`. By `roosLift_χ`, its coordinates
  are `(0,(λ_n)_n)`.
- This fixes exactly the exact-products negative-difference fibre comparison
  followed by `(y,x) ↦ (-y,x)`: that sign change preserves the inclusion. On
  K-injective towers both unit and inclusion are invertible, so the equation
  determines the comparison. Naturality and K-injective replacement determine
  it on every complex. The unit equation therefore retains both the sign and
  arbitrary-complex clauses and does not allow an unspecified cone isomorphism.
- `projection_natural` and `boundary_natural` retain naturality on derived
  strict towers. The cone comparison and the shift comparison are natural
  isomorphisms. The product maps are canonical natural product constructions.
- The existential `σ` has type `shift ⋙ d.direct ≅ d.direct ⋙ shift`.
  Its equation on every complex `L` is precisely
  `σ_Q(L) η_(L[1]) = η_L[1]`, with all ordinary and localization shift
  identifications explicit. No arbitrary shift structure is assumed.
- `d.direct.map (T.projection M) ≫ productMap d M =
  d.comparison.hom.app M ≫ U.projection (d.tower.obj M)` is the first square.
- The last equation is the connecting square. Its left side consists of
  `d.direct.map (T.boundary M)`, the unit-normalized `σ`, and
  `(d.comparison.hom.app M)⟦1⟧'`. Its first component is exactly the given
  normalized `d.comparison`, not an existential map between cone vertices.

Dependency declarations read and used (modules and names):

- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, including the full induced-module
  direct-image and generalized-element compatibility fields.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the transparent abbreviation of
  Mathlib's general-site `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, its localization and shift interfaces, and
  `DerivedCategory.mappingCocone_triangle_distinguished`.
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`:
  `CategoryTheory.ringedTowerPushforwardLimitComparison`. The full unit,
  ordinary-comparison and evaluation equations are packaged in `DirectImageData`.
  The existing theorem remains a proof dependency.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
  `LimitData` packages its total-derived-limit and evaluation choices.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle` and `IsDerivedLimit`.
- `Sheaf.CategoryTheory.StrictRoosModel`: `CategoryTheory.roosF`, `roosP`,
  `roosU`, `roosProj`, `roosLift`, and their coordinate/inclusion lemmas.
- `Sheaf.Algebra.Homology.ExactProductsRoosComparison`:
  `CategoryTheory.ExactProductsRoos.comparisonIso`; its `ordinary`,
  `inclusion` and proved `inclusion_difference` construct the actual inclusion.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective` supplies the
  K-injective unit convention and proof plan.

All stated proof-dependency modules are imported, including additive Roos
comparison, K-injective products, the exact-adjoint criterion, degreewise
K-injective resolutions, tower evaluation and triangulated derivation. The
upstream `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
import exposes the small-site sheaf instances. This repaired an initial
elaboration failure without adding an assumption. The site and module
universes follow the recorded small-site interface. The localization universe
`w` remains independent. All universes and variables are explicitly bound.

Edge cases checked: zero rings and zero modules are permitted; zero complexes,
identity transitions and zero transitions are permitted; complexes need not be
bounded; representing complexes need not be K-injective. Unit normalization
holds on every complex, while K-injectivity only specifies the dependency's
computation property. The positive countable index is nonempty by definition.
Shift equations include the localization comparisons, without assuming strict
equality of shifted derived objects. The sign change preserves the zero first
coordinate of the ordinary-limit inclusion.

Searches before writing:

- `msearch.py`, LeanFinder: `Canonical derived direct image comparison preserves
  normalized Roos triangles including the connecting morphism`. Eight hits,
  headed by `Triangulated.SpectralObject.mapTriangulatedFunctor_δ` and abstract
  triangulated-functor results; none states this normalized tower comparison.
- `msearch.py`, Loogle: `CategoryTheory.Limits.piComparison,
  CategoryTheory.Triangle.Hom`. Zero hits; the second candidate name is unknown.
  Direct inspection then used the actual triangle/mapping-cocone interfaces.
- `msearch.py`, Mathlib grep: `Roos|rightDerived.*commShift` in
  `Algebra/Homology`. Zero hits. Ordinary cone/shift APIs found by direct reading
  do not state this result for a nonexact direct image.
- `msearch.py`, LeanSearch: `The canonical derived direct image inverse limit
  isomorphism gives a morphism of the normalized Roos triangles including
  connecting maps`. Eight hits, including limit isomorphisms and
  `CochainComplex.mappingCone.mapTrianglehIso`; none states this theorem.
- Direct `rg` in `lean/Sheaf`, `lean/WeilConjectures`, Mathlib and
  `dag/lean_names_upstream.json` for `Roos`, `roos`, the item id, direct-image
  Roos combinations and proposed names. Found the recorded constructions and
  unrelated integral direct-image triangles, but no exact statement or name
  collision. No upstream file contains this item id.
- Read `StrictRoosNormalization`, `StrictRoosDerivedLimitComparison` and
  `RingedStrictTowerProjectionMorphism` to check nearby interfaces; none states
  the direct-image three-square result with the fixed first component.

Sources opened: Stacks `sites-cohomology.tex`,
`lemma-Rf-commutes-with-Rlim` (Tag 0A07), and `derived.tex`,
`lemma-product-K-injective` (Tag 0BK6); all recorded statement dependencies'
source signatures and docstrings. The example CompactObject module is now
withdrawn; its node points to the identical upstream module, which was read.

Validation: `scompile.py` compiled both sandbox and final module names without
errors or warnings. The final direct proof imports are checked again by the
required dry run, which also runs server preflight. No statement dispute or
correction is recorded. The maintainer provides the independent second reading.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
