# WeilConjectures.LisseRealization.RealizationTensorComparison

## Reason

Move the five existing comparison-data declarations to the new shared module
`Sheaf.Paper.LisseTensorPullbackRealizationData`. The three proof-step modules need these
interfaces, and the item needs their conclusions. Keeping the interfaces in the item would
create an import cycle. This is an acyclic dependency refactoring, not a response to a compile
time limit. No field, universe, parameter, attribute, visibility or construction changes.
The original module publicly imports the data module, retaining its public interface.

The moved declarations are `realizationOrdinaryTensor`, `RealizationTensorCalculation`,
`RealizationTensorCalculation.arrow`, `RealizationTensorComparison`, and
`RealizationPullComparison`, all in namespace `WeilConjectures.LisseRealization`.
Their signatures and complete bodies were checked byte for byte with the original declarations.
No target statement or definition meaning changes, so no semantic target review is reopened.

DAG record of the move (reviewer, 2026-10-25): the five declarations are now owned by the new
node `def-real-tensor-pullback-comparison-data`, and the statement of
`lem-tw-lisse-tensor-pullback-realization` uses `RealizationTensorComparison` and
`RealizationPullComparison`; its `stmt_deps` therefore gain
`def-real-tensor-pullback-comparison-data`. The statement text is unchanged.

## Old

In `Sheaf.Paper.LisseTensorPullbackRealization`, with its existing namespace and variables:

```lean
/-- The published ordinary ambient derived tensor over the localized coefficient sheaf.
Source: Stacks 06YU; BS 6.8.15
(blueprint: lem-tw-lisse-tensor-pullback-realization). -/
abbrev realizationOrdinaryTensor (X : Base D l hl) :=
  SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u, u + 1, u + 2}
    (ProEt.topology X.scheme) (rationalCoefficientSheaf l X.scheme E)

/-- Calculation of the tensor comparison on every pair of good integral representatives.
The two scalar counits, the signed-total representative comparison, and the specified chi
fix the entire derived arrow, rather than only its map on degree-zero homology.
Source: BS 6.8.15 and Stacks 07A4
(blueprint: lem-tw-lisse-tensor-pullback-realization). -/
structure RealizationTensorCalculation {X : Base D l hl} (a : At D l hl E X)
    (K L : sfIntegralConstructibleCategory l E X.scheme)
    (P Q : (integralOperationsGoodComplex l E X.scheme).FullSubcategory)
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ L.obj) where
  model : TensorModel D l hl E a K L P Q eP eQ
  kflatP : CochainComplex.IsKFlatIndependentCoefficients (rationalComplex D l hl E a P.obj)
  kflatQ : CochainComplex.IsKFlatIndependentCoefficients (rationalComplex D l hl E a Q.obj)
  flatP : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
    (J := ProEt.topology X.scheme) (R := rationalCoefficientSheaf l X.scheme E)
    ((rationalComplex D l hl E a P.obj).X n)
  flatQ : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
    (J := ProEt.topology X.scheme) (R := rationalCoefficientSheaf l X.scheme E)
    ((rationalComplex D l hl E a Q.obj).X n)
  left : DerivedCategory.Q.obj (rationalComplex D l hl E a P.obj) ≅
    (pbcDerivedExtend (scalar D l hl E a)).obj K.obj
  left_normalized : left.inv =
    (pbcDerivedExtend (scalar D l hl E a)).map eP.inv ≫
      pbcComplexCounit (scalar D l hl E a) P.obj
  right : DerivedCategory.Q.obj (rationalComplex D l hl E a Q.obj) ≅
    (pbcDerivedExtend (scalar D l hl E a)).obj L.obj
  right_normalized : right.inv =
    (pbcDerivedExtend (scalar D l hl E a)).map eQ.inv ≫
      pbcComplexCounit (scalar D l hl E a) Q.obj

/-- The tensor arrow prescribed by the inverse completion, scalar associators and
ordinary K-flat tensor comparison. Every ingredient is fixed by a section or counit equation.
Source: BS 6.8.15; Stacks 07A4
(blueprint: lem-tw-lisse-tensor-pullback-realization). -/
def RealizationTensorCalculation.arrow {X : Base D l hl} {a : At D l hl E X}
    {K L : sfIntegralConstructibleCategory l E X.scheme}
    {P Q : (integralOperationsGoodComplex l E X.scheme).FullSubcategory}
    {eP : DerivedCategory.Q.obj P.obj ≅ K.obj}
    {eQ : DerivedCategory.Q.obj Q.obj ≅ L.obj}
    (m : RealizationTensorCalculation D l hl E a K L P Q eP eQ) :=
  (pbcDerivedExtend (scalar D l hl E a)).map m.model.completed.inv ≫
    pbcComplexCounit (scalar D l hl E a)
      ((constructibleTensorTotal l E X.scheme).obj (P.obj, Q.obj)) ≫
    DerivedCategory.Q.map m.model.scalar.hom ≫
    (SheafOfModules.KFlatFixedTensor.representativeIso
      (rationalCoefficientSheaf l X.scheme E)
      (rationalComplex D l hl E a P.obj) (rationalComplex D l hl E a Q.obj)
      m.kflatP m.kflatQ m.flatP m.flatQ).hom ≫
    (realizationOrdinaryTensor D l hl E X).map (Prod.mkHom m.left.hom m.right.hom)

/-- The full derived tensor comparison, its scalar-one unit and its lisse specialization.
The model condition quantifies over all good representatives, including those with torsion
in integral cohomology. Source: BS 6.8.15
(blueprint: lem-tw-lisse-tensor-pullback-realization). -/
structure RealizationTensorComparison (X : Base D l hl) (a : At D l hl E X) where
  lisse : TensorAt D l hl E X a
  normalized : TensorNormalized D l hl E X a lisse
  comparison : constructibleIntegralTensor l E X.scheme ⋙
      (sfIntegralConstructible l E X.scheme).ι ⋙ pbcDerivedExtend (scalar D l hl E a) ≅
    (((sfIntegralConstructible l E X.scheme).ι ⋙ pbcDerivedExtend (scalar D l hl E a)).prod
      ((sfIntegralConstructible l E X.scheme).ι ⋙ pbcDerivedExtend (scalar D l hl E a))) ⋙
        realizationOrdinaryTensor D l hl E X
  models : ∀ (K L : sfIntegralConstructibleCategory l E X.scheme)
    (P Q : (integralOperationsGoodComplex l E X.scheme).FullSubcategory)
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ L.obj),
    ∃ m : RealizationTensorCalculation D l hl E a K L P Q eP eQ,
      HEq (comparison.hom.app (K, L)) (m.arrow D l hl E)
  raw : tensor D l hl E X ⋙ a.J ≅ (a.J.prod a.J) ⋙ realizationOrdinaryTensor D l hl E X
  integral : ∀ K L : sfIntegralConstructibleCategory l E X.scheme,
    HEq (raw.hom.app ((sfRationalConstructibleLocalization l E X.scheme).obj K,
      (sfRationalConstructibleLocalization l E X.scheme).obj L))
      (a.integral.hom.app ((constructibleIntegralTensor l E X.scheme).obj (K, L)) ≫
        comparison.hom.app (K, L) ≫
        (realizationOrdinaryTensor D l hl E X).map
          (Prod.mkHom (a.integral.inv.app K) (a.integral.inv.app L)))
  degree_zero : ∀ (K L : Raw D l hl E X) (hK : Lisse D l hl E X K)
    (hL : Lisse D l hl E X L),
    ∃ e : (realizationOrdinaryTensor D l hl E X).obj (a.J.obj K, a.J.obj L) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((a.sheaf D l hl E).obj K ⊗ (a.sheaf D l hl E).obj L),
      (DerivedCategory.homologyFunctor _ 0).map ((raw.app (K, L)).hom ≫ e.hom) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _ =
      (lisse.tensor K L hK hL).hom
  unit : (pbcExtend (scalar D l hl E a)).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme)) ≅
    SheafOfModules.unit ((adicLisseForget X.scheme).obj (rationalCoefficientSheaf l X.scheme E))
  unit_sections : ∀ (U : X.scheme.ProEtᵒᵖ)
    (c : (rationalCoefficientSheaf l X.scheme E).obj.obj U)
    (b : (completedIntegralCommRingSheafUnrestricted l E X.scheme).obj.obj U),
    unit.hom.val.app U (pbcTensorSection (scalar D l hl E a)
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))
      U c b) = c * ((scalar D l hl E a).hom.app U b)


  derived_unit : (pbcDerivedExtend (scalar D l hl E a)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))) ≅
    (DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit ((adicLisseForget X.scheme).obj
        (rationalCoefficientSheaf l X.scheme E)))
  derived_unit_normalized : derived_unit.hom =
    (pbcDerivedExtend (scalar D l hl E a)).map
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app _) ≫
      pbcComplexCounit (scalar D l hl E a)
        ((CochainComplex.singleFunctor _ 0).obj
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (pbcExtend (scalar D l hl E a)) (.up ℤ) 0).hom.app _) ≫
      (DerivedCategory.singleFunctorIsoCompQ (Modules D l hl E X) 0).inv.app
        ((pbcExtend (scalar D l hl E a)).obj
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))) ≫
      (DerivedCategory.singleFunctor _ 0).map unit.hom

/-- Natural comparison on all raw rational objects, restricting to the specified inverse
eta and scalar square on integral representatives. The recorded normalization includes the
ordinary adjunction-unit square, the derived counit square, and identity on H^0.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-tw-lisse-tensor-pullback-realization). -/
structure RealizationPullComparison {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme)
    (aX : At D l hl E X) (aY : At D l hl E Y) where
  lisse : Along D l hl E f aX aY
  normalized : PullNormalized D l hl E f aX aY lisse
  comparison : pull D l hl E f ⋙ aX.J ≅
    aY.J ⋙ ContinuousRational.derivedPull f (coefficientPull l E f)
  integral : ∀ K : sfIntegralConstructibleCategory l E Y.scheme,
    (comparison.app ((sfRationalConstructibleLocalization l E Y.scheme).obj K)).hom =
      (normalized.comparison K).hom
```

## New

The exact declarations now live in `Sheaf.Paper.LisseTensorPullbackRealizationData` with the
same namespace, universes, variables, options and public visibility:

```lean
/-- The published ordinary ambient derived tensor over the localized coefficient sheaf.
Source: Stacks 06YU; BS 6.8.15
(blueprint: lem-tw-lisse-tensor-pullback-realization). -/
abbrev realizationOrdinaryTensor (X : Base D l hl) :=
  SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u, u + 1, u + 2}
    (ProEt.topology X.scheme) (rationalCoefficientSheaf l X.scheme E)

/-- Calculation of the tensor comparison on every pair of good integral representatives.
The two scalar counits, the signed-total representative comparison, and the specified chi
fix the entire derived arrow, rather than only its map on degree-zero homology.
Source: BS 6.8.15 and Stacks 07A4
(blueprint: lem-tw-lisse-tensor-pullback-realization). -/
structure RealizationTensorCalculation {X : Base D l hl} (a : At D l hl E X)
    (K L : sfIntegralConstructibleCategory l E X.scheme)
    (P Q : (integralOperationsGoodComplex l E X.scheme).FullSubcategory)
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ L.obj) where
  model : TensorModel D l hl E a K L P Q eP eQ
  kflatP : CochainComplex.IsKFlatIndependentCoefficients (rationalComplex D l hl E a P.obj)
  kflatQ : CochainComplex.IsKFlatIndependentCoefficients (rationalComplex D l hl E a Q.obj)
  flatP : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
    (J := ProEt.topology X.scheme) (R := rationalCoefficientSheaf l X.scheme E)
    ((rationalComplex D l hl E a P.obj).X n)
  flatQ : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
    (J := ProEt.topology X.scheme) (R := rationalCoefficientSheaf l X.scheme E)
    ((rationalComplex D l hl E a Q.obj).X n)
  left : DerivedCategory.Q.obj (rationalComplex D l hl E a P.obj) ≅
    (pbcDerivedExtend (scalar D l hl E a)).obj K.obj
  left_normalized : left.inv =
    (pbcDerivedExtend (scalar D l hl E a)).map eP.inv ≫
      pbcComplexCounit (scalar D l hl E a) P.obj
  right : DerivedCategory.Q.obj (rationalComplex D l hl E a Q.obj) ≅
    (pbcDerivedExtend (scalar D l hl E a)).obj L.obj
  right_normalized : right.inv =
    (pbcDerivedExtend (scalar D l hl E a)).map eQ.inv ≫
      pbcComplexCounit (scalar D l hl E a) Q.obj

/-- The tensor arrow prescribed by the inverse completion, scalar associators and
ordinary K-flat tensor comparison. Every ingredient is fixed by a section or counit equation.
Source: BS 6.8.15; Stacks 07A4
(blueprint: lem-tw-lisse-tensor-pullback-realization). -/
def RealizationTensorCalculation.arrow {X : Base D l hl} {a : At D l hl E X}
    {K L : sfIntegralConstructibleCategory l E X.scheme}
    {P Q : (integralOperationsGoodComplex l E X.scheme).FullSubcategory}
    {eP : DerivedCategory.Q.obj P.obj ≅ K.obj}
    {eQ : DerivedCategory.Q.obj Q.obj ≅ L.obj}
    (m : RealizationTensorCalculation D l hl E a K L P Q eP eQ) :=
  (pbcDerivedExtend (scalar D l hl E a)).map m.model.completed.inv ≫
    pbcComplexCounit (scalar D l hl E a)
      ((constructibleTensorTotal l E X.scheme).obj (P.obj, Q.obj)) ≫
    DerivedCategory.Q.map m.model.scalar.hom ≫
    (SheafOfModules.KFlatFixedTensor.representativeIso
      (rationalCoefficientSheaf l X.scheme E)
      (rationalComplex D l hl E a P.obj) (rationalComplex D l hl E a Q.obj)
      m.kflatP m.kflatQ m.flatP m.flatQ).hom ≫
    (realizationOrdinaryTensor D l hl E X).map (Prod.mkHom m.left.hom m.right.hom)

/-- The full derived tensor comparison, its scalar-one unit and its lisse specialization.
The model condition quantifies over all good representatives, including those with torsion
in integral cohomology. Source: BS 6.8.15
(blueprint: lem-tw-lisse-tensor-pullback-realization). -/
structure RealizationTensorComparison (X : Base D l hl) (a : At D l hl E X) where
  lisse : TensorAt D l hl E X a
  normalized : TensorNormalized D l hl E X a lisse
  comparison : constructibleIntegralTensor l E X.scheme ⋙
      (sfIntegralConstructible l E X.scheme).ι ⋙ pbcDerivedExtend (scalar D l hl E a) ≅
    (((sfIntegralConstructible l E X.scheme).ι ⋙ pbcDerivedExtend (scalar D l hl E a)).prod
      ((sfIntegralConstructible l E X.scheme).ι ⋙ pbcDerivedExtend (scalar D l hl E a))) ⋙
        realizationOrdinaryTensor D l hl E X
  models : ∀ (K L : sfIntegralConstructibleCategory l E X.scheme)
    (P Q : (integralOperationsGoodComplex l E X.scheme).FullSubcategory)
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ L.obj),
    ∃ m : RealizationTensorCalculation D l hl E a K L P Q eP eQ,
      HEq (comparison.hom.app (K, L)) (m.arrow D l hl E)
  raw : tensor D l hl E X ⋙ a.J ≅ (a.J.prod a.J) ⋙ realizationOrdinaryTensor D l hl E X
  integral : ∀ K L : sfIntegralConstructibleCategory l E X.scheme,
    HEq (raw.hom.app ((sfRationalConstructibleLocalization l E X.scheme).obj K,
      (sfRationalConstructibleLocalization l E X.scheme).obj L))
      (a.integral.hom.app ((constructibleIntegralTensor l E X.scheme).obj (K, L)) ≫
        comparison.hom.app (K, L) ≫
        (realizationOrdinaryTensor D l hl E X).map
          (Prod.mkHom (a.integral.inv.app K) (a.integral.inv.app L)))
  degree_zero : ∀ (K L : Raw D l hl E X) (hK : Lisse D l hl E X K)
    (hL : Lisse D l hl E X L),
    ∃ e : (realizationOrdinaryTensor D l hl E X).obj (a.J.obj K, a.J.obj L) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((a.sheaf D l hl E).obj K ⊗ (a.sheaf D l hl E).obj L),
      (DerivedCategory.homologyFunctor _ 0).map ((raw.app (K, L)).hom ≫ e.hom) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _ =
      (lisse.tensor K L hK hL).hom
  unit : (pbcExtend (scalar D l hl E a)).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme)) ≅
    SheafOfModules.unit ((adicLisseForget X.scheme).obj (rationalCoefficientSheaf l X.scheme E))
  unit_sections : ∀ (U : X.scheme.ProEtᵒᵖ)
    (c : (rationalCoefficientSheaf l X.scheme E).obj.obj U)
    (b : (completedIntegralCommRingSheafUnrestricted l E X.scheme).obj.obj U),
    unit.hom.val.app U (pbcTensorSection (scalar D l hl E a)
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))
      U c b) = c * ((scalar D l hl E a).hom.app U b)


  derived_unit : (pbcDerivedExtend (scalar D l hl E a)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))) ≅
    (DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit ((adicLisseForget X.scheme).obj
        (rationalCoefficientSheaf l X.scheme E)))
  derived_unit_normalized : derived_unit.hom =
    (pbcDerivedExtend (scalar D l hl E a)).map
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app _) ≫
      pbcComplexCounit (scalar D l hl E a)
        ((CochainComplex.singleFunctor _ 0).obj
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (pbcExtend (scalar D l hl E a)) (.up ℤ) 0).hom.app _) ≫
      (DerivedCategory.singleFunctorIsoCompQ (Modules D l hl E X) 0).inv.app
        ((pbcExtend (scalar D l hl E a)).obj
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))) ≫
      (DerivedCategory.singleFunctor _ 0).map unit.hom

/-- Natural comparison on all raw rational objects, restricting to the specified inverse
eta and scalar square on integral representatives. The recorded normalization includes the
ordinary adjunction-unit square, the derived counit square, and identity on H^0.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-tw-lisse-tensor-pullback-realization). -/
structure RealizationPullComparison {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme)
    (aX : At D l hl E X) (aY : At D l hl E Y) where
  lisse : Along D l hl E f aX aY
  normalized : PullNormalized D l hl E f aX aY lisse
  comparison : pull D l hl E f ⋙ aX.J ≅
    aY.J ⋙ ContinuousRational.derivedPull f (coefficientPull l E f)
  integral : ∀ K : sfIntegralConstructibleCategory l E Y.scheme,
    (comparison.app ((sfRationalConstructibleLocalization l E Y.scheme).obj K)).hom =
      (normalized.comparison K).hom
```

The item reexports them using:

```lean
public import Sheaf.Paper.LisseTensorPullbackRealizationData
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseTensorPullbackRealization | B4 | Same theorem signature; its proof assembles the split steps. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Unmodified consumer compiled successfully against all changed modules; the two comparison structures retain every field. |
| Sheaf.Paper.DerivedTensorRealization | new, B4 | Uses the moved model calculation and ordinary tensor. |
| Sheaf.Paper.TensorHeartSpecialization | new, B4 | Uses the same tensor interface through DerivedTensorRealization. |
| Sheaf.Paper.IntegralLissePullbackNormalization | new, B4 | Uses the same pullback normalization interface. |

`tools/downstream.py Sheaf.Paper.LisseTensorPullbackRealization` finds exactly the point-sections
module downstream. Its `--uses` scans of both comparison structures agree. No source-library
module is modified. No existing consumer requires a forced adaptation.

## Status

landed 20261025T122527-L-1780869 2026-10-25 (merge of deliver/B4/Sheaf.Paper.LisseTensorPullbackRealization)
