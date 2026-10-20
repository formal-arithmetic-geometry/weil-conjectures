# AlgebraicGeometry.Scheme.FiniteFreeDirectImage normalized coefficient data

## Reason

The two separate source calculations (finite-basis columns and balancing units/towers)
need the existing data types without importing the theorem whose proof uses them.
Move those unchanged declarations from FiniteFreeDirectImageCoherence to
FiniteFreeDirectImageData, publicly reexported by the original module. No definition
body, declaration name, signature, universe or visibility changes. Only blueprint
comments point to the new definition node. In particular the balancing is still the
inverse adjunction conjugate of the published restriction/direct-image isomorphism,
and comparison is still its actual right mate.

Remove unused Paper imports. They formerly supplied the global instance attributes
for proEtaleRingRestrictScalars_preservesFiniteLimits and
proEtaleRingRestrictScalars_preservesFiniteColimits through FourCorners. Data explicitly
preserves those same attributes on those same existing proved declarations.
No new instance theorem or proof is introduced.

Profiling a delivery timeout identified automatic SizeOf generation for ScalarModel:
Meta.sizeOf took 19.9 seconds, alongside expensive generated size specifications.
Disable only that automatic generation with `set_option genSizeOf false in` on the
structure. Its fields, constructor and projections are unchanged; the unused generated
SizeOf instance and its support declarations are absent. No consumer uses them.
The data module then compiled in 15.3 seconds, instead of the profiled 54.8/58.3
seconds. This is not a file split or an increased compiler time limit.

## Old

In lean/Sheaf/AlgebraicGeometry/FiniteFreeDirectImageCoherence.lean:

```lean
abbrev Presentation (X : Scheme.{u}) {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) :=
  SheafOfModules.SuccessiveDerivedQuotient.Presentation.{u + 1, u, u + 1, u + 2}
    (C := X.ProEt) (J := ProEt.topology X) (R := R) (S := S)
    (hD := fun T ↦ proEtaleRingModules_hasDerivedCategory X T) a

/-- A normalized family of the existing scalar functors, with its multiplication unit.
`presentation` fixes ordinary objects and maps and the universal derived counit;
`normalization` fixes the balanced associators and tensor units. The additional
adjunction is normalized against exact scalar restriction, and the multiplication
isomorphism is fixed by its ordinary pure-tensor formula and the universal counit.
Source: Stacks Tags 03EK, 06YY and 07A6
(blueprint: lem-sp-finite-free-direct-image-coherence). -/
structure ScalarModel (X : Scheme.{u}) where
  /-- Existing universal scalar-extension pairs, without a second tensor definition. -/
  presentation : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}},
    (a : R ⟶ S) → Presentation X a
  /-- The recorded balanced associator and its K-flat normalization. -/
  normalization :
    SheafOfModules.SuccessiveDerivedQuotient.Normalization.{u + 1, u, u + 1, u + 2}
      (C := X.ProEt) (J := ProEt.topology X)
      (hD := fun T ↦ proEtaleRingModules_hasDerivedCategory X T) presentation
  /-- Scalar adjunction to the actual exact restriction, rather than an unrelated functor. -/
  adjunction : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S),
    (presentation a).derived ⊣ (proEtaleRingRestrictScalars a).mapDerivedCategory
  /-- Normalization of the derived scalar unit at every flat-term K-flat complex. -/
  adjunction_unit : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (proEtaleRingModules X R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := R) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := R) (P.X n)) →
    (adjunction a).unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategory.map
        ((presentation a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.hom.app
        (((presentation a).ordinary.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) =
    DerivedCategory.Qh.map
      (((normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P))
  /-- Multiplication `r ⊗ x ↦ r x` before localization. -/
  ordinaryUnit : ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
    (presentation (𝟙 R)).ordinary ≅ 𝟭 (proEtaleRingModules X R)
  /-- The pure-tensor normalization determines the ordinary unit uniquely. -/
  ordinaryUnit_pure : ∀ (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : proEtaleRingModules X R) (U : X.ProEtᵒᵖ) (r : R.obj.obj U) (x : M.val.obj U),
    ((ordinaryUnit R).hom.app M).val.app U
      (SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
        (presentation (𝟙 R)) M U r x) = r • x
  /-- Multiplication after the universal derived scalar extension. -/
  unit : ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
    (presentation (𝟙 R)).derived ≅ 𝟭 (DerivedCategory (proEtaleRingModules X R))
  /-- The derived multiplication is determined by its universal counit. -/
  unit_normalization : ∀ (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (H : HomotopyCategory (proEtaleRingModules X R) (.up ℤ)),
    (unit R).hom.app (DerivedCategory.Qh.obj H) =
      (presentation (𝟙 R)).counit.app H ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (ordinaryUnit R).hom (.up ℤ)).app H) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryIdIso (proEtaleRingModules X R) (.up ℤ)).hom.app H)

/-- The canonical scalar shift is the adjoint of the termwise restriction shift.
Source: Stacks Tag 07A6 (blueprint: lem-sp-finite-free-direct-image-coherence). -/
instance scalarCommShift {X : Scheme.{u}} (s : ScalarModel X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (s.presentation a).derived.CommShift ℤ :=
  (s.adjunction a).leftAdjointCommShift ℤ

/-- The coefficient ring at both ends, with the specified inverse-image identification.
Source: Stacks Tag 0B56 (blueprint: lem-sp-finite-free-direct-image-coherence). -/
structure Coefficients {Z W : Scheme.{u}} (q : Z ⟶ W) where
  /-- Ring sheaf on the target. -/
  target : Sheaf (ProEt.topology W) CommRingCat.{u + 1}
  /-- Ring sheaf on the source. -/
  source : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}
  /-- The specified identification of inverse-image coefficients. -/
  identification : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj target ≅ source

/-- Compatible coefficient maps on the two sites; the only condition is the ring square.
Source: Stacks Tag 0B56 (blueprint: lem-sp-finite-free-direct-image-coherence). -/
structure CoefficientMap {Z W : Scheme.{u}} {q : Z ⟶ W} (R S : Coefficients q) where
  /-- Coefficient map on the target. -/
  target : R.target ⟶ S.target
  /-- Coefficient map on the source. -/
  source : R.source ⟶ S.source
  /-- The inverse-image identifications commute with coefficient change. -/
  comm : R.identification.hom ≫ source =
    (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map target ≫ S.identification.hom

/-- Identity coefficient map, keeping the given geometric identification.
Source: Stacks Tag 0B56 (blueprint: lem-sp-finite-free-direct-image-coherence). -/
def CoefficientMap.id {Z W : Scheme.{u}} {q : Z ⟶ W} (R : Coefficients q) :
    CoefficientMap R R where
  target := 𝟙 _
  source := 𝟙 _
  comm := by simp

/-- Composition of compatible coefficient maps, using the same identifications.
Source: Stacks Tag 0D6D (blueprint: lem-sp-finite-free-direct-image-coherence). -/
def CoefficientMap.comp {Z W : Scheme.{u}} {q : Z ⟶ W} {R S B : Coefficients q}
    (a : CoefficientMap R S) (b : CoefficientMap S B) : CoefficientMap R B where
  target := a.target ≫ b.target
  source := a.source ≫ b.source
  comm := by
    rw [← Category.assoc, a.comm, Category.assoc, b.comm, Functor.map_comp,
      Category.assoc]

/-- Canonical balancing, obtained by conjugating the actual normalized right adjoints.
The right-adjoint comparison is the published one fixed by its derived units and its
identity section maps. Scalar adjunctions have the `x ↦ 1 ⊗ x` normalization, so this
conjugate is exactly the balanced scalar/pullback comparison, including on flat K-flat
representatives. Its definition does not use the finite-free theorem below.
Source: Stacks Tags 03EL, 0D6D and 07A6
(blueprint: lem-sp-finite-free-direct-image-coherence). -/
def balancing {Z W : Scheme.{u}} {q : Z ⟶ W} (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S) :
    (sW.presentation a.target).derived ⋙
        proEtaleRingDerivedPullback q S.target S.source S.identification ≅
      proEtaleRingDerivedPullback q R.target R.source R.identification ⋙
        (sZ.presentation a.source).derived :=
  ((conjugateIsoEquiv
      ((sW.adjunction a.target).comp
        (proEtaleRingDerivedAdjunction q S.target S.source S.identification))
      ((proEtaleRingDerivedAdjunction q R.target R.source R.identification).comp
        (sZ.adjunction a.source))).symm
    (proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)).symm

/-- The actual counit-tensor comparison in the larger coefficient derived category.
By the mate formula its component is the `Lq_S* ⊣ Rq_S*` adjunct of
`balancing.hom ≫ C_Z(ε_R)`. No scalar-forgetting functor is used to define the arrow.
Source: Stacks Tag 0B56 (blueprint: lem-sp-finite-free-direct-image-coherence). -/
def comparison {Z W : Scheme.{u}} {q : Z ⟶ W} (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S) :
    proEtaleRingDerivedDirectImage q R.target R.source R.identification ⋙
        (sW.presentation a.target).derived ⟶
      (sZ.presentation a.source).derived ⋙
        proEtaleRingDerivedDirectImage q S.target S.source S.identification :=
  (mateEquiv
    (proEtaleRingDerivedAdjunction q R.target R.source R.identification)
    (proEtaleRingDerivedAdjunction q S.target S.source S.identification)
    (TwoSquare.mk _ _ _ _ (balancing sW sZ a).hom)).natTrans
```

## New

In lean/Sheaf/AlgebraicGeometry/FiniteFreeDirectImageData.lean:

```lean
abbrev Presentation (X : Scheme.{u}) {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) :=
  SheafOfModules.SuccessiveDerivedQuotient.Presentation.{u + 1, u, u + 1, u + 2}
    (C := X.ProEt) (J := ProEt.topology X) (R := R) (S := S)
    (hD := fun T ↦ proEtaleRingModules_hasDerivedCategory X T) a

set_option genSizeOf false in
/-- A normalized family of the existing scalar functors, with its multiplication unit.
`presentation` fixes ordinary objects and maps and the universal derived counit;
`normalization` fixes the balanced associators and tensor units. The additional
adjunction is normalized against exact scalar restriction, and the multiplication
isomorphism is fixed by its ordinary pure-tensor formula and the universal counit.
Source: Stacks Tags 03EK, 06YY and 07A6
(blueprint: def-sp-finite-free-direct-image-data). -/
structure ScalarModel (X : Scheme.{u}) where
  /-- Existing universal scalar-extension pairs, without a second tensor definition. -/
  presentation : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}},
    (a : R ⟶ S) → Presentation X a
  /-- The recorded balanced associator and its K-flat normalization. -/
  normalization :
    SheafOfModules.SuccessiveDerivedQuotient.Normalization.{u + 1, u, u + 1, u + 2}
      (C := X.ProEt) (J := ProEt.topology X)
      (hD := fun T ↦ proEtaleRingModules_hasDerivedCategory X T) presentation
  /-- Scalar adjunction to the actual exact restriction, rather than an unrelated functor. -/
  adjunction : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S),
    (presentation a).derived ⊣ (proEtaleRingRestrictScalars a).mapDerivedCategory
  /-- Normalization of the derived scalar unit at every flat-term K-flat complex. -/
  adjunction_unit : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (proEtaleRingModules X R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := R) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := R) (P.X n)) →
    (adjunction a).unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategory.map
        ((presentation a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.hom.app
        (((presentation a).ordinary.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) =
    DerivedCategory.Qh.map
      (((normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P))
  /-- Multiplication `r ⊗ x ↦ r x` before localization. -/
  ordinaryUnit : ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
    (presentation (𝟙 R)).ordinary ≅ 𝟭 (proEtaleRingModules X R)
  /-- The pure-tensor normalization determines the ordinary unit uniquely. -/
  ordinaryUnit_pure : ∀ (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : proEtaleRingModules X R) (U : X.ProEtᵒᵖ) (r : R.obj.obj U) (x : M.val.obj U),
    ((ordinaryUnit R).hom.app M).val.app U
      (SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
        (presentation (𝟙 R)) M U r x) = r • x
  /-- Multiplication after the universal derived scalar extension. -/
  unit : ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
    (presentation (𝟙 R)).derived ≅ 𝟭 (DerivedCategory (proEtaleRingModules X R))
  /-- The derived multiplication is determined by its universal counit. -/
  unit_normalization : ∀ (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (H : HomotopyCategory (proEtaleRingModules X R) (.up ℤ)),
    (unit R).hom.app (DerivedCategory.Qh.obj H) =
      (presentation (𝟙 R)).counit.app H ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (ordinaryUnit R).hom (.up ℤ)).app H) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryIdIso (proEtaleRingModules X R) (.up ℤ)).hom.app H)

/-- The canonical scalar shift is the adjoint of the termwise restriction shift.
Source: Stacks Tag 07A6 (blueprint: def-sp-finite-free-direct-image-data). -/
instance scalarCommShift {X : Scheme.{u}} (s : ScalarModel X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (s.presentation a).derived.CommShift ℤ :=
  (s.adjunction a).leftAdjointCommShift ℤ

/-- The coefficient ring at both ends, with the specified inverse-image identification.
Source: Stacks Tag 0B56 (blueprint: def-sp-finite-free-direct-image-data). -/
structure Coefficients {Z W : Scheme.{u}} (q : Z ⟶ W) where
  /-- Ring sheaf on the target. -/
  target : Sheaf (ProEt.topology W) CommRingCat.{u + 1}
  /-- Ring sheaf on the source. -/
  source : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}
  /-- The specified identification of inverse-image coefficients. -/
  identification : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj target ≅ source

/-- Compatible coefficient maps on the two sites; the only condition is the ring square.
Source: Stacks Tag 0B56 (blueprint: def-sp-finite-free-direct-image-data). -/
structure CoefficientMap {Z W : Scheme.{u}} {q : Z ⟶ W} (R S : Coefficients q) where
  /-- Coefficient map on the target. -/
  target : R.target ⟶ S.target
  /-- Coefficient map on the source. -/
  source : R.source ⟶ S.source
  /-- The inverse-image identifications commute with coefficient change. -/
  comm : R.identification.hom ≫ source =
    (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map target ≫ S.identification.hom

/-- Identity coefficient map, keeping the given geometric identification.
Source: Stacks Tag 0B56 (blueprint: def-sp-finite-free-direct-image-data). -/
def CoefficientMap.id {Z W : Scheme.{u}} {q : Z ⟶ W} (R : Coefficients q) :
    CoefficientMap R R where
  target := 𝟙 _
  source := 𝟙 _
  comm := by simp

/-- Composition of compatible coefficient maps, using the same identifications.
Source: Stacks Tag 0D6D (blueprint: def-sp-finite-free-direct-image-data). -/
def CoefficientMap.comp {Z W : Scheme.{u}} {q : Z ⟶ W} {R S B : Coefficients q}
    (a : CoefficientMap R S) (b : CoefficientMap S B) : CoefficientMap R B where
  target := a.target ≫ b.target
  source := a.source ≫ b.source
  comm := by
    rw [← Category.assoc, a.comm, Category.assoc, b.comm, Functor.map_comp,
      Category.assoc]

/-- Canonical balancing, obtained by conjugating the actual normalized right adjoints.
The right-adjoint comparison is the published one fixed by its derived units and its
identity section maps. Scalar adjunctions have the `x ↦ 1 ⊗ x` normalization, so this
conjugate is exactly the balanced scalar/pullback comparison, including on flat K-flat
representatives. Its definition does not use the finite-free theorem below.
Source: Stacks Tags 03EL, 0D6D and 07A6
(blueprint: def-sp-finite-free-direct-image-data). -/
def balancing {Z W : Scheme.{u}} {q : Z ⟶ W} (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S) :
    (sW.presentation a.target).derived ⋙
        proEtaleRingDerivedPullback q S.target S.source S.identification ≅
      proEtaleRingDerivedPullback q R.target R.source R.identification ⋙
        (sZ.presentation a.source).derived :=
  ((conjugateIsoEquiv
      ((sW.adjunction a.target).comp
        (proEtaleRingDerivedAdjunction q S.target S.source S.identification))
      ((proEtaleRingDerivedAdjunction q R.target R.source R.identification).comp
        (sZ.adjunction a.source))).symm
    (proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)).symm

/-- The actual counit-tensor comparison in the larger coefficient derived category.
By the mate formula its component is the `Lq_S* ⊣ Rq_S*` adjunct of
`balancing.hom ≫ C_Z(ε_R)`. No scalar-forgetting functor is used to define the arrow.
Source: Stacks Tag 0B56 (blueprint: def-sp-finite-free-direct-image-data). -/
def comparison {Z W : Scheme.{u}} {q : Z ⟶ W} (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S) :
    proEtaleRingDerivedDirectImage q R.target R.source R.identification ⋙
        (sW.presentation a.target).derived ⟶
      (sZ.presentation a.source).derived ⋙
        proEtaleRingDerivedDirectImage q S.target S.source S.identification :=
  (mateEquiv
    (proEtaleRingDerivedAdjunction q R.target R.source R.identification)
    (proEtaleRingDerivedAdjunction q S.target S.source S.identification)
    (TwoSquare.mk _ _ _ _ (balancing sW sZ a).hom)).natTrans
```

The original module now has:

```lean
public import Sheaf.AlgebraicGeometry.FiniteFreeDirectImageData
```

and the data module retains the previously available attributes explicitly:

```lean
attribute [instance] proEtaleRingRestrictScalars_preservesFiniteLimits
  proEtaleRingRestrictScalars_preservesFiniteColimits
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence --uses
FiniteFreeDirectImage ScalarModel balancing comparison` reports zero current Lean
importers. The original theorem remains attached to its node and remains needed by
its unfinished DAG parents; none is withdrawn. Its statement is verbatim unchanged.
The definitions used by Challenge do not change meaning, so no semantic target change
is proposed. Public reexport retains access through the old module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence | N4 | Same public declarations through Data; theorem proved by the new route. |
| Sheaf.AlgebraicGeometry.FiniteFreeDirectImageData | N4, new | Same record fields and definitions; suppress unused SizeOf generation; retain exactness attributes. |
| Sheaf.AlgebraicGeometry.FiniteFreeDirectImageColumns | N4, new | Imports Data to state the finite-basis column calculation without a cycle. |
| Sheaf.AlgebraicGeometry.FiniteFreeDirectImageBalancingCoherence | N4, new | Imports Data to state the separate left-balancing calculation without a cycle. |
| Sheaf.AlgebraicGeometry.FiniteFreeDirectImageScalarModels | N4, new | Constructs the normalized models of Data. |
| Sheaf.AlgebraicGeometry.FiniteFreeDirectImageScalarShift | N4, new | Proves shift and triangulatedness for these unchanged models. |
| Sheaf.AlgebraicGeometry.FiniteFreeDirectImageShift | N4, new | Proves shift compatibility for the unchanged comparison. |

No module of another group and no WeilConjectures declaration is adapted.

## Status

landed 20261020T221301-L-4168742 2026-10-20 (merge of deliver/N4/Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence)
