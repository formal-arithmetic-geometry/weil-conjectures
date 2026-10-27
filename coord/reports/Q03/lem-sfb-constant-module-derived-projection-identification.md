## Worker report

The delivery states the original item without changing its statement, proof, or proof dependencies. The main theorem is `CategoryTheory.ConstantModuleDerivedProjection.constant_module_derived_projection_identification`. The specialized theorem `etale_constant_module_derived_projection_identification` and its `EtaleIdentification` package state the last clause. All theorems have `sorry` proofs and source/proof docstrings. The helper definitions contain actual structures, subtypes and equations, not choices of unproved existence witnesses.

Hypotheses and clauses, read in order:

- Sites small relative to the coefficient universe: `{C D : Type u} [Category.{v} C] [Category.{v} D]`, `J`, `K`, and `A : Type (max u v)`. The independent `u,v` admit small étale sites with objects in `Type (z+1)` and morphisms in `Type z`. No equality of these universes is imposed. `[CommRing A] [Finite A]` renders the finite discrete coefficient ring; discreteness here means the algebraic module category, with no topology or completion.
- The geometric morphism and constant-section-preserving isomorphism are `GeometricData.inverse`, `direct`, `geometric`, `leftExact`, `algebraic`, `scalarIso`, `terminalIso`, and `constants`. The last is equality on generalized constant scalar maps, without points. `ringed` and its compatibility fields retain the recorded ringed-topos notion, its structural ring operations, and induced module action.
- The fixed coefficient and ringed categories are the recorded `ConstantScalarRestriction.Fixed`, `Modules`, `ring`, and `restriction`. Restriction is the inverse direction of the equivalences denoted E in the item; it preserves the underlying additive sheaf. Its exact equivalence, flat/K-flat preservation and signed-total comparison are imported from `ConstantScalarRestrictionTensor`; they are not redefined.
- `pullR`, `object_eq`, `map_eq` use actual `changeOfRings` after `AlgebraicInverseImage.modules`. `ringTensor` is the recorded `CanonicalRingedTensorComparison`, whose q is insertion of 1 and whose mu is the specified generalized pure-tensor isomorphism. `ringAdj`, `pushUnderlying`, and `ringHom` normalize the ordinary ringed adjunction on underlying sheaves. The fixed-scalar adjunction is `FixedScalarGeometricAdjunctionOfUniverses`, owned by this delivery's geometric-data module, with its induced scalar-linear direct-image equation. Thus no arbitrary action or arbitrary pullback map replaces the canonical construction.
- `ExactData` is existential in the theorem's conclusion. It records the exactness and coproduct preservation consequences required by the localization API; it adds no assumption to the theorem.
- All derived categories are Mathlib `DerivedCategory`, with explicit `HasDerivedCategory.{w}` size choices. These are ordinary localizations at quasi-isomorphisms. The monoidal structures are the existing K-flat monoidal structures, cached rather than constructed afresh. The representative predicate uses `IsKFlatForTotalTensor`, which the recorded scalar theorem identifies with the acyclic total-tensor definition. The flatness definition is the recorded exactness-of-tensor definition.
- `OrdinaryIdentification.left`, `right`, `underlying`, `hom` state the normalized ordinary scalar comparison. `FixedTensorData.underlying`, `hom`, `monoidal`, `pure` specify the fixed-ring pullback tensor map, with its generalized pure-tensor equation and its geometric Hom normalization.
- The two input `DerivedComparison` values are the normalized scalar tensor comparisons of the recorded scalar theorem. The theorem works for every such normalized comparison. `DerivedTensorIdentification` includes both derived pullback monoidal structures, ordinary ringed tensor normalization, two `TensorNormalization` localization equations on K-flat total representatives. `DerivedIdentification` adds `TensorSquare` for all derived objects. Thus equality holds for every pair of unbounded inputs; it is not limited to perfect objects or a bounded tensor factor.
- `DerivedIdentification.left`, `right` intertwine pullbacks and right derived direct images. `LeftLocalizationSquare` and `RightLocalizationSquare` recover the specified ordinary comparisons through the canonical localization/derived-functor factor maps. `AdjunctionSquare` states the full Hom bijection equation and the unit and counit equations for `mapDerivedCategoryRightDerivedAdjunction`, the canonical K-injective-derived adjunction.
- `DerivedIdentification.projection` is `ProjectionSquare` for the existing `Adjunction.rightAdjointProjectionMap` applied to the specified tensor comparison. Its equation includes both scalar tensorators, the left and right comparison isomorphisms and their functorial images. It is natural in both inputs, because the maps are components of the existing bifunctor natural transformation. No projection invertibility is asserted.
- `PlusIdentification` uses `DerivedCategory.Plus`, the full subcategory with cohomology vanishing below an integer. Its left and right inclusion equations use `DerivedCategory.Plus.ι` and `rightDerivedFunctorPlusCompatibility`. Its Hom equation retains the bounded-below adjunction, and its `ring_counit` and `fixed_counit` identify each included bounded-below counit with the unbounded counit using the canonical comparison isomorphisms. It makes no assertion that unbounded tensor preserves D+.
- The étale theorem uses the actual small étale sites, `Scheme.etaleSetPullback`, `Etale.lowerStar` on sets, and equalities with the actual module `Etale.upperStar` and `lowerStar`. The ordinary adjunction is explicitly identified with `upperStarLowerStarAdjunction`. The ringed geometric datum retains the prescribed transported module action and underlying-sheaf Hom normalization. The `EtaleIdentification` specialization of `NormalizedComparison` has `left_normalized`, which uses `leftDerivedUpperStarIsoMapDerivedCategory`; `right_normalized` uses the canonical derived natural isomorphism. Its Hom equation identifies the actual étale derived adjunction. Its `tensor_square` uses `leftDerivedUpperStarMonoidal`, whose tensorator is definitionally the published `leftDerivedUpperStarTensorComparison`, the inverse orientation of the isomorphism in the monoidality node. Its projection equation uses the same adjunction and tensorator that definitionally define the actual `rightDerivedLowerStarProjectionMap`. The identity scalar functors in this specialization simply identify the two functor realizations. Composing with the general scalar square gives the specified ringed projection map, as required.

Dependency declarations used (module followed by declaration):

- `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`: `CategoryTheory.ConstantScalarRestriction.ring`, `Modules`, `Fixed`, `restriction`, `onComplexes`, `onDerived`, `DerivedComparison`, `derived_comparison`, `flat_iff`, `kflat_iff`.
- `Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence`: `CategoryTheory.site_moduleSheaf_constantRing_equivalence`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: the unchanged recorded
  `CategoryTheory.RingedToposMorphism`. The independent-universe extension
  `CategoryTheory.RingedToposMorphismOfUniverses` belongs to
  `Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData`.
- `Sheaf.CategoryTheory.ConstantScalarGeometricAdjunctions`: the unchanged recorded
  `CategoryTheory.FixedScalarGeometricAdjunction` and
  `CategoryTheory.constant_scalar_geometric_adjunctions`. The corresponding
  `FixedScalarGeometricAdjunctionOfUniverses` and
  `constant_scalar_geometric_adjunctions_ofUniverses` helpers belong to
  `Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `CategoryTheory.DerivedCategory`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`, with `CanonicalRingedTensorComparison` and `AlgebraicInverseImage` supplied by its imported interfaces.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`.
- `WeilConjectures.CategoryTheory.Adjunction.ProjectionMap`: `CategoryTheory.Adjunction.rightAdjointProjectionMap`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`: `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`: `CategoryTheory.Adjunction.derivedPlus`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`: `CategoryTheory.Functor.rightDerivedFunctorPlusCompatibility`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: `AlgebraicGeometry.etaleInverseImageModulesExact`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`: `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso`, `leftDerivedUpperStarTensorComparison`, `leftDerivedUpperStarIsoMapDerivedCategory`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`: `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`.

The remaining proof-dependency modules are imported as the stage-3 proof plan, including exact-equivalence localization, K-injective resolutions and Hom calculation, ordinary module adjunction and tensor-section calculus, K-flat resolutions, signed cochain tensor coherence, resolving tensor descent, and bounded-below injective representatives.

Edge cases read before finalizing: A=0 does not require a nonzero scalar or division; identity geometric morphisms retain the canonical units and counits rather than merely endpoint equivalences; empty sites/topoi introduce no point or nonempty-section assumption; A=Z/4 and arbitrary two-sided unbounded complexes are admitted, with K-flat resolution rather than termwise flatness of the inputs; the small étale site has independent object and morphism universes. No characteristic, scheme, finiteness of cohomological dimension, existence of points, tensor bound or projection-isomorphism assumption was added to the general theorem.

Searches: `msearch.py` LeanFinder query “Constant scalar equivalences identify derived tensor pullback adjunction and projection formula maps for ringed topoi” returned ordinary pullback-adjunction unit/counit and pullback-composition lemmas, not this derived statement. Loogle `SheafOfModules, "projection"` and Mathlib grep `constant.*(derived|projection)|projection.*constant` in CategoryTheory returned no match. The module and target-id searches in `lean/WeilConjectures`, and scalar/derived/projection searches in `lean/Sheaf`, found the dependencies used above but no declaration of the combined statement. The exact queries and original result summaries for new notions are preserved in each new node's `mathlib_searches`.

There is no mathematical statement correction or STATEMENT-DISPUTED finding.

## Second reading by Q03

I reread the node and signatures clause by clause, including all four definition nodes and the independent-universe helpers. The dispatcher explicitly starts this worker without a lead and prohibits starting another agent; this is a worker self-check, not a claim of independent review. The maintainer's independent review reads this delivery. The self-check caught the need to retain localization squares, the full étale comparison, and the distinction between site object and morphism universes; all are explicit in the delivered interfaces.

## New nodes

`def-sfb-derived-projection-comparison-squares` defines tensor, adjunction and projection commuting-square predicates and the K-flat total normalization predicate. Source: Stacks 07A4 and 07A6. LeanSearch returned general `CatCommSq` and monoidal-functor constructors, LeanFinder returned total-complex component formulas, and Mathlib grep found no exact predicate. DAG/blueprint, upstream and Sheaf searches found no existing node for these normalized packages. The existing projection morphism is reused.

`def-sfb-constant-module-geometric-comparison-data` packages the actual geometric, ringed and fixed-scalar module data with generalized-element normalizations, ordinary scalar comparison, exactness consequences and normalized derived tensor square. Source: Stacks 03EL, 07A4 and 07A6. LeanSearch returned constant-sheaf adjunctions and ordinary module pullback constructions; LeanFinder returned unrelated scalar restriction names; grep found ordinary constant-sheaf material. No existing node supplies the package. Every underlying scalar restriction, algebraic lift and ringed tensor notion is imported rather than copied.

`def-sfb-constant-module-derived-comparison-data` packages localization, full derived adjunction, tensor and projection equations. Source: Stacks 07A4, 07A6 and derived.tex 013K/070J. The same package search found component APIs but no combined normalized datum; the new node records the exact search results. Blueprint search and DAG grep found no such node. These definitions assert no existence theorem.

`def-sfb-constant-module-plus-comparison-data` packages the bounded-below comparison, its canonical inclusion squares, full Hom equation and included-counit equations. Source: Stacks 07A6 and derived.tex 013K/070J. The comparison-data LeanSearch, LeanFinder and grep searches recorded in this node found component APIs but no such normalized package. It uses the unbounded comparison node and the existing `DerivedCategory.Plus`, `derivedPlus` and `rightDerivedFunctorPlusCompatibility`; it introduces no second derived category or derived functor.

## Repair of return L at 6574ec191ae2

The returned H13/H4 fault was a rebind of two already-landed dependency records.
Both `def-weil-pbc-ringed-topos-morphism` and
`lem-sfb-constant-scalar-geometric-adjunctions` are now byte-identical to the live
node files, including their entire lean records. Neither dependency node or landed
module is changed by this delivery. The old declarations remain imported.

The three generalized helpers `RingedToposMorphismOfUniverses`,
`FixedScalarGeometricAdjunctionOfUniverses` and
`constant_scalar_geometric_adjunctions_ofUniverses` now reside in
`ConstantModuleGeometricComparisonData.lean`, owned by
`def-sfb-constant-module-geometric-comparison-data`, and are listed in that node's
lean.declarations. Their source and ownership docstrings are retained, with the
helper theorem's complete proof plan. The generalized structure signatures and
theorem conclusions are unchanged. The two separate helper modules are removed
from the packet. This is the reviewer's explicitly requested ownership repair,
not a replacement of the live small-category interfaces.

The original mathematical item and its two theorem signatures remain unchanged.
All previously checked tensor, localization, Hom, unit, counit, projection and
bounded-below equations remain present. Self-check compared each moved declaration
with the saved version; only its ownership tag and location changed, and the new
ringed structure's additive projection is registered as an instance.

Advisory from L: the inverse-image clause of
`prop-weil-pbc-inverse-image-modules-exact` is rendered using the actual
`AlgebraicGeometry.Etale.upperStar (ModuleCat B)` and the identified
`upperStarLowerStarAdjunction`, rather than by citing the dependency theorem
inside the signature. Its published module is imported. The etale datum's
set-sheaf `d.geometric` is not separately equated with a chosen set-sheaf
adjunction; the actual module adjunction is pinned by the displayed `HEq`, and
the derived Hom and projection equations use that actual module adjunction.

## Validation

The saved seven-module packet first passed the prescribed dry run; that mechanical
check did not detect the independent review's dependency-rebinding fault. After
the repair, five modules remain. Compilation and preflight results are recorded
below after rerunning the prescribed wrappers. The two restored dependency copies
are checked against the live files and must not appear in the staged delivery.

After the ownership repair, `scompile.py` passed all five delivered modules
separately in dependency order with no errors or unexpected warnings. The library
checks took 9.2 s (comparison squares), 37.0 s (geometric data and generalized
helpers), 52.8 s (derived data), 3.4 s (bounded-below data), and 6.3 s (main item).
Every check stayed within the prescribed 60-second limit. The self-check confirms
100-character Lean lines, explicit universes and `autoImplicit false` in every
module, exactly the three intended postponed named theorems, and no data defined
by `sorry`. The main item differs from live only in lean and added definition
stmt_deps. Both restored dependency node files match the live bytes exactly.

The repaired `deliver2.py --no-push` run passed server compilation and preflight
(commit 0b612c01e8c). Its staged list contains exactly the five owned modules,
the item plus four definition nodes, and this report. Neither restored dependency
node nor either old landed module appears in that list. Primary lean.statement
signatures were also checked verbatim against all five delivered source files.

## Maintainer review fix (df5e8cb69be7)

The name `CategoryTheory.RingedToposMorphismOfUniverses` is already landed: it is in
`Sheaf.Paper.SequenceSiteCompletionProjection`, owned by the DAG node
`def-pur-ringed-topos-morphism-of-universes` (Q111, existing: true, 2026-10-21). That
version is more general, with independent object and morphism universes and an
`EssentiallySmall.{r}` coefficient universe. Its fields are the same as the copy this
delivery placed in `ConstantModuleGeometricComparisonData.lean`. Two declarations with the
same full name would clash in any module that imports both, and the copy duplicates a
notion that a DAG node already carries (H4/H9/H12).

The reviewer's fix makes four changes:

- **Copy removed.** The geometric-data module now public-imports
  `Sheaf.Paper.SequenceSiteCompletionProjection` instead of defining its own copy.
- **Landed structure used.** `GeometricData.ringed` and
  `constant_scalar_geometric_adjunctions_ofUniverses` use the landed structure at
  `r = max u v`, with the instances `essentiallySmallSelf.{v}`.
- **Node record updated.** `def-sfb-constant-module-geometric-comparison-data` gains the
  stmt_dep `def-pur-ringed-topos-morphism-of-universes`, and the removed name is dropped
  from its declarations.
- **Instance erased in the item module.** The imported `SemilinearSystemModels` declares a
  global instance `WeilConjectures.SemilinearSections.hasDerived`, a standard localization
  for every ring-sheaf module category. It took over the etale `HasDerivedCategory`
  synthesis, so the item module now erases it locally with `attribute [-instance]`. After
  that the etale clause again uses `HasDerivedCategory.ofIsGrothendieckAbelian`, as before.

The item statement is unchanged.
