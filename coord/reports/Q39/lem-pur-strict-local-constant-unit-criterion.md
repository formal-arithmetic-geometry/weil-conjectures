## Worker report

The module `Sheaf.AlgebraicGeometry.StrictLocalConstantUnitCriterion` states
`AlgebraicGeometry.Etale.strictLocal_constant_unit_criterion`. Its sole theorem has
proof `sorry`. Six accompanying helpers are compositions or specializations of
existing constructions, with actual data throughout. No definition node or
statement correction is needed. The original node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- Schemes and the given morphism: `{Y X : Scheme.{u}} (f : Y ⟶ X)`.
- Quasi-compact and quasi-separated morphism: `[QuasiCompact f] [QuasiSeparated f]`.
  There is no compactness, separation, or Noetherian assumption on either scheme.
- Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- Finite Λ-module: `(B : ModuleCat.{u + 1} Λ) [Finite B]`. Over a finite ring,
  finite underlying set and finitely generated module are equivalent notions of
  finite module. The abelian coefficient is the actual coefficientwise forgetful
  image `(forget₂ (ModuleCat Λ) AddCommGrpCat).obj B`.
- Constant sheaf `B_T` and placement in degree zero: `constantSheafSingle A T B`
  abbreviates `(DerivedCategory.Plus.singleFunctor _ 0).obj
  ((constantSheaf T.smallEtaleTopology A).obj B)`. It introduces no alternative
  constant sheaf or derived category.
- Every geometric point: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ X)` in both the hypothesis and normalization conclusion.
- Strict local base and fibre: `Scheme.strictLocalizationToBase x` and
  `pullback f (Scheme.strictLocalizationToBase x)`. The source's strictLocalization
  is the recorded strict-henselization spectrum; its structural-map extension
  supplies the same affine-neighbourhood limit map. The pullback projections in
  the comparison are `pullback.fst` and `pullback.snd` of these exact arrows.
- The hypothesis `B[0] → RΓ(Y ×_X S_x, B)` is an isomorphism:
  `h` is `IsIso (constantDerivedSectionsMap AddCommGrpCat ... B_ab)` for every
  point. This helper is the derived unit of `constantSheafΓAdj`, followed by
  the canonical compatibility of exact constants with `singleFunctor`. Its
  target is the ordinary `Sheaf.Γ.rightDerivedFunctorPlus`, not compact supports.
- The abelian unit is invertible: the first conjunct is `IsIso
  (constantDerivedDirectImageUnit AddCommGrpCat f B_ab)`.
- The fixed-Λ module unit is invertible: the second conjunct is `IsIso
  (constantDerivedDirectImageUnit (ModuleCat Λ) f B)` in its actual module
  derived category. The helper in either category is the unit of
  `upperStarLowerStarAdjunction.derivedPlus`, followed by derived direct image
  of the exact-single comparison and `Scheme.upperStarConstantSheafIso`.
- Canonical restriction identification: the remaining conclusion supplies a
  natural isomorphism `r` from the actual abelian stalk to strict-local sections
  after inverse image, with `∀ F, IsStrictHenselizationStalkRestriction x F
  (r.hom.app F)`. This predicate specifies its composite with every representative
  affine pointed germ, not only its endpoints. The existing unique-existence
  theorem makes this a unique restriction; `r` is a concluded canonical object,
  not an additional input or an arbitrary selected isomorphism.
  `strictLocalConstantDerivedRestriction` derives this specified isomorphism,
  applies exact sections to the canonical derived pullback-square mate, passes
  from exact sections to derived sections, applies the canonical Leray isomorphism,
  and finally uses the single/constant inverse-image identification. The third
  clause asserts that this full map is invertible in `D⁺(Ab)`.
- Exact unit normalization: the final equality is
  `constantDerivedGeometricGerm B_ab x ≫ (constantUnitDerivedStalk x).map
  (constantDerivedDirectImageUnit AddCommGrpCat f B_ab) ≫
  strictLocalConstantDerivedRestriction f x r B_ab =
  constantDerivedSectionsMap AddCommGrpCat (pullback f ...) B_ab`.
  This is equality of the actual morphisms in `DerivedCategory.Plus AddCommGrpCat`.
  The constant germ helper uses exactly the recorded sheafification unit at
  `Etale.mk (𝟙 X)` followed by the pointed stalk germ, then the exact-single
  isomorphism. The derived-stalk helper applies the recorded exact fibre functor
  termwise; existing `AB5OfSize_shrink` and `sheafFiber_additive` supply its
  mathematical structures without imposing any universe equality or new premise.

The canonical comparison is made explicit by the existential `r` only because
its existing interface states unique existence on individual sheaves. No theorem
or unspecified choice is used as data in a new definition. The theorem states
its naturality/isomorphism together with the prescribed components and the derived
normalization, so this representation does not silently weaken the canonical-map
clause. All helpers belong to that clause and are listed in `lean.declarations`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`,
  with `Scheme.Etale` from `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`
  and `toSheafify`; `Mathlib.CategoryTheory.Sites.GlobalSections`:
  `Sheaf.Γ` and `constantSheafΓAdj`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and the scheme pullback instance.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, and `Etale.upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `Etale.rightDerivedLowerStarPlus`; its definition is the ordinary right
  derived functor of the recorded direct image.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  the recorded `DerivedCategory.Plus` and module-sheaf encoding. The main
  theorem uses this encoding with `ModuleCat.{u+1} Λ` and `AddCommGrpCat.{u+1}`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalkDiagram`,
  `pointedEtaleStalk`, `pointedEtaleGerm`. The specialized functor used here is
  the existing `Scheme.pointSmallEtale x |>.sheafFiber`, with precisely the same
  colimit diagram, as the dependency docstring specifies. No new stalk is defined.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, `Scheme.strictHenselizationScheme`;
  `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`:
  `Scheme.strictLocalization`, `Scheme.strictLocalizationToBase`;
  `StrictHenselizationStructuralMapExtension` identifies the adopted constructions.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the recorded site convention
  `Precoverage.IsSiteForCoverings` is imported; ordinary cohomology uses the
  existing derived sections functor rather than defining new cohomology.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction`:
  `IsStrictHenselizationStalkRestriction`,
  `strictHenselization_globalSections_preservesFiniteColimits`.
- `WeilConjectures.ConstructibleSheaf.Defs`:
  `Scheme.upperStarConstantSheafIso`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryPlus`, `mapDerivedCategoryPlusSingleFunctor`,
  `mapDerivedCategoryPlusNatIso`, `mapDerivedCategoryPlusCompIso`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `Adjunction.derivedPlus`; `PlusComp`: `rightDerivedFunctorPlusCompIso'`;
  `PlusExact`: `rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`.
  `Etale.lowerStarCompGlobalSectionsIso` and the pullback-square comparison fix
  the Leray and mate constructions.
- The already stated proof dependencies are imported without public visibility:
  `StrictHenselizationStalkFormula` (the adopted upstream module, the old Sheaf
  file is withdrawn), `PullbackConstantModule`, `ConstantSheafGeometricStalk`,
  `DerivedGeometricStalkConservative`, `ConstantModuleSectionCoefficients`,
  `ModuleAbelianDerivedDirectImageComparison`. Their declaration names are
  respectively `Etale.strictHenselizationStalkFormula`,
  `Scheme.pullback_constantModule_isIso`, `Scheme.constantSheaf_geometricStalk_isIso`,
  `Scheme.isIso_iff_isIso_geometricStalk_homologyMap`,
  `Etale.constantModuleSectionCoefficientEquiv`, and
  `Etale.isIso_moduleAbelianDerivedLowerStarComparison`.
  The cohomology detection leaf is `DerivedCategory.Plus.isIso_iff` (Mathlib).
  Exact stalks are the existing Point finite-limit and left-adjoint constructions.

Sources checked: Stacks `etale-cohomology.tex`,
`theorem-higher-direct-images` (03Q9), especially its last paragraph constructing
an actual derived restriction by maps of section complexes. The imported
restriction and coefficient-comparison modules supply the source normalizations
from 03PT, 03FD and 0D6J; the proof docstring reproduces all five DAG proof steps.
No statement fault or STATEMENT-DISPUTED issue was found.

Edge cases checked mathematically:

- `X` empty: the universal hypothesis over points is vacuous, and the conclusion
  still applies to the zero sheaf categories. There is no nonempty instance.
- `B = 0`, including the zero ring: every displayed arrow is between zero objects.
- Empty strict-local fibre at an existing point: its derived sections are zero,
  so the hypothesis forces `B = 0`; no false nonzero coefficient case is asserted.
- `f = id`: the ordinary derived unit is invertible and the normalization agrees
  with the constant germ and strict-local sections comparison.
- `Y = X ⊔ X` with nonzero coefficients and a geometric point: the constants
  diagonal to two copies fails to be an isomorphism, as the hypothesis requires.
- Negative degrees are retained by `D⁺`; there is no degree-zero-only or per-degree
  weakening. The fixed coefficient universe is the established six-functor size
  convention, not an extra smallness restriction on a finite ring or finite module.

Searches actually run:

- `msearch.py leanfinder`: “For a qcqs scheme morphism the constant module derived
  unit is invertible if constants induce a cohomology isomorphism on every strict
  henselization fibre”. Eight hits concerning formally unramified morphisms,
  affine Γ/Spec units and module stalks; no matching derived criterion.
- `msearch.py loogle`: `"constantSheaf", "unit"`. Three constant-sheaf counit
  results; none is this direct-image unit criterion.
- `msearch.py grep`: `strict.*hensel.*stalk|constantSheaf.*unit`. Nine hits, in
  condensed constant-module comparisons and constant-sheaf counits; no criterion.
- `msearch.py leansearch`: “The constant derived direct image unit is an
  isomorphism if the constants map on every strict henselization base change is
  an isomorphism”. Eight hits about constant-sheaf counits, monoidal localization,
  condensed constants, Γ/Spec and `constantCommuteCompose`; no exact match.
- `rg` in both project roots for the item id: no existing declaration. Searches
  for strict-local/constant-unit module names located the adopted strict-local
  stalk and exchange constructions and `FiniteConstantUnitRestriction`; reading
  the latter showed it is a different pro-etale open-unit implication, not this
  small-etale criterion. `StrictLocalDerivedExchangeGlobalSections` and
  `StrictLocalAbelianTotalExchange` concern the mate comparison, not its constant
  unit normalization or this detection theorem.
- `rg` across Mathlib, `WeilConjectures`, `Sheaf`, and `dag/lean_names_upstream.json`
  for all seven chosen declaration names returned no prior declarations.

Validation: the entire module compiled separately against the live server library
using `scompile.py`, both as a sandbox probe and under its library module name,
without errors or warnings. Final delivery preflight and compile are run by
`deliver2.py` after writing this record and report.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
