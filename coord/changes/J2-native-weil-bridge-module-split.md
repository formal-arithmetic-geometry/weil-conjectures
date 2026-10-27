# AlgebraicGeometry.ProEtaleWeilSheaf.NativeWeilTensorRingedBridge

## Reason

Separate the existing bridge data from its construction to meet the 60-second
per-file compilation limit. Profiling the combined file showed over 80 seconds
of type checking before the complete construction was checked. The definition,
field types and instance attributes are preserved verbatim; only their module
location changes. The original module publicly imports the new data module.

## Old

In Sheaf.Paper.NativeWeilTensorRingedBridge:

```lean
structure NativeWeilTensorRingedBridge
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] where
  /-- The action site. -/
  C : Type (u + 1)
  [categoryC : SmallCategory C]
  J : GrothendieckTopology C
  R : Sheaf J CommRingCat.{u + 1}
  /-- The ordinary small pro-etale site. -/
  A : Type (u + 1)
  [categoryA : SmallCategory A]
  K : GrothendieckTopology A
  Q : Sheaf K CommRingCat.{u + 1}
  /-- Equivalences of actual module categories, before localization. -/
  native : ProEtaleWeilSheaf k₀ l X ≌ RingedTensorModules.{u + 1, u + 1, u + 1} J R
  ordinary : ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≌
    RingedTensorModules.{u + 1, u + 1, u + 1} K Q
  [native_additive : native.functor.Additive]
  [ordinary_additive : ordinary.functor.Additive]
  /-- Restriction from the action site. -/
  forget : RingedTensorModules.{u + 1, u + 1, u + 1} J R ⥤
    RingedTensorModules.{u + 1, u + 1, u + 1} K Q
  [forget_additive : forget.Additive]
  [forget_limits : PreservesFiniteLimits forget]
  [forget_colimits : PreservesFiniteColimits forget]
  [forget_products : ∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) forget]
  [forget_coproducts : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) forget]
  [forget_injectives : forget.PreservesKInjectiveComplexes]
  /-- The functor in this square is exactly native underived forgetting. -/
  square : native.functor ⋙ forget ≅
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ⋙ ordinary.functor
  /-- Restriction has the normalized sheaf tensor, unit, Hom and evaluation maps. -/
  underived : RingedForgetTensorTransposition.Underived J R K Q forget
  /-- The native equivalence preserves the underived internal Hom. -/
  nativeHom : Functor.uncurry.obj (ihomBifunctor k₀ l X) ⋙ native.functor ≅
    (native.functor.op.prod native.functor) ⋙
      Functor.uncurry.obj (SheafOfModules.homFunctor (R := R))
  /-- The ordinary equivalence preserves the underived internal Hom. -/
  ordinaryHom : Functor.uncurry.obj
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⋙
        ordinary.functor ≅
    (ordinary.functor.op.prod ordinary.functor) ⋙
      Functor.uncurry.obj (SheafOfModules.homFunctor (R := Q))
  /-- These are the same Hom comparison across the square, including evaluation. -/
  hom_square (P I : ProEtaleWeilSheaf k₀ l X) :
    forget.map (nativeHom.hom.app (op P, I)) ≫
        underived.hom.hom.app (op (native.functor.obj P), native.functor.obj I) ≫
        SheafOfModules.homObjMap (R := Q) (square.inv.app P) (square.hom.app I) ≫
        ordinaryHom.inv.app (op P.carrier, I.carrier) =
      square.hom.app (((ihomBifunctor k₀ l X).obj (op P)).obj I)
  /-- The native coefficient module is the genuine ringed tensor unit. -/
  nativeUnit : native.functor.obj (adicConstant k₀ l X) ≅
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  /-- Restriction takes flat-term K-flat complexes to flat-term K-flat complexes. -/
  preserves_flat_models (P : CochainComplex
      (RingedTensorModules.{u + 1, u + 1, u + 1} J R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients)
      (hterms : ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X p)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := Q)
      ((forget.mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := Q) (forget.obj (P.X p))
```

## New

The identical declaration, in Sheaf.Paper.NativeWeilTensorRingedBridgeData:

```lean
structure NativeWeilTensorRingedBridge
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] where
  /-- The action site. -/
  C : Type (u + 1)
  [categoryC : SmallCategory C]
  J : GrothendieckTopology C
  R : Sheaf J CommRingCat.{u + 1}
  /-- The ordinary small pro-etale site. -/
  A : Type (u + 1)
  [categoryA : SmallCategory A]
  K : GrothendieckTopology A
  Q : Sheaf K CommRingCat.{u + 1}
  /-- Equivalences of actual module categories, before localization. -/
  native : ProEtaleWeilSheaf k₀ l X ≌ RingedTensorModules.{u + 1, u + 1, u + 1} J R
  ordinary : ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≌
    RingedTensorModules.{u + 1, u + 1, u + 1} K Q
  [native_additive : native.functor.Additive]
  [ordinary_additive : ordinary.functor.Additive]
  /-- Restriction from the action site. -/
  forget : RingedTensorModules.{u + 1, u + 1, u + 1} J R ⥤
    RingedTensorModules.{u + 1, u + 1, u + 1} K Q
  [forget_additive : forget.Additive]
  [forget_limits : PreservesFiniteLimits forget]
  [forget_colimits : PreservesFiniteColimits forget]
  [forget_products : ∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) forget]
  [forget_coproducts : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) forget]
  [forget_injectives : forget.PreservesKInjectiveComplexes]
  /-- The functor in this square is exactly native underived forgetting. -/
  square : native.functor ⋙ forget ≅
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ⋙ ordinary.functor
  /-- Restriction has the normalized sheaf tensor, unit, Hom and evaluation maps. -/
  underived : RingedForgetTensorTransposition.Underived J R K Q forget
  /-- The native equivalence preserves the underived internal Hom. -/
  nativeHom : Functor.uncurry.obj (ihomBifunctor k₀ l X) ⋙ native.functor ≅
    (native.functor.op.prod native.functor) ⋙
      Functor.uncurry.obj (SheafOfModules.homFunctor (R := R))
  /-- The ordinary equivalence preserves the underived internal Hom. -/
  ordinaryHom : Functor.uncurry.obj
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⋙
        ordinary.functor ≅
    (ordinary.functor.op.prod ordinary.functor) ⋙
      Functor.uncurry.obj (SheafOfModules.homFunctor (R := Q))
  /-- These are the same Hom comparison across the square, including evaluation. -/
  hom_square (P I : ProEtaleWeilSheaf k₀ l X) :
    forget.map (nativeHom.hom.app (op P, I)) ≫
        underived.hom.hom.app (op (native.functor.obj P), native.functor.obj I) ≫
        SheafOfModules.homObjMap (R := Q) (square.inv.app P) (square.hom.app I) ≫
        ordinaryHom.inv.app (op P.carrier, I.carrier) =
      square.hom.app (((ihomBifunctor k₀ l X).obj (op P)).obj I)
  /-- The native coefficient module is the genuine ringed tensor unit. -/
  nativeUnit : native.functor.obj (adicConstant k₀ l X) ≅
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  /-- Restriction takes flat-term K-flat complexes to flat-term K-flat complexes. -/
  preserves_flat_models (P : CochainComplex
      (RingedTensorModules.{u + 1, u + 1, u + 1} J R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients)
      (hterms : ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X p)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := Q)
      ((forget.mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := Q) (forget.obj (P.X p))
```

The original module now has `public import Sheaf.Paper.NativeWeilTensorRingedBridgeData`.
Its two previous public imports accompany the data declaration, so the public
transitive import closure remains available. All instance attributes move with
their declarations.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeWeilTensorRingedBridge | J2 | same record re-exported by `public import`; construction supplied |
| Sheaf.Paper.NativeWeilTensorRingedStructure | unclaimed | direct importer; identical names, fields and instances remain public; compiled against the delivery |
| Sheaf.Paper.NativeWeilTensorRingedComplexes | unclaimed | direct importer; identical names, fields and instances remain public; compiled against the delivery |
| Sheaf.Paper.NativeWeilTensorRingedModel | unclaimed | transitive user of the name; no signature or proof changes |
| Sheaf.Paper.NativeWeilTensorRingedModelNaturality | unclaimed | transitive user of the name; no signature or proof changes |
| Sheaf.Paper.NativeWeilTensorRingedComplexModel | unclaimed | transitive user of the name; no signature or proof changes |
| Sheaf.Paper.NativeWeilTensorRingedDerivedSquare | unclaimed | transitive user of the name; no signature or proof changes |
| Sheaf.Paper.NativeWeilTensorRingedTransport | unclaimed | transitive user of the name; no signature or proof changes |
| Sheaf.Paper.NativeWeilTensorGeometry | unclaimed | transitive user of the name; no signature or proof changes |

These are all modules that mention the moved name (two direct importers of the
original module and six transitive users). The public import closure of the
original module is unchanged: it publicly imports the data module, which publicly
imports the two previous public imports. No consumer is adapted. Target meanings
and all five target signatures are unchanged.

## Status

landed 20261027T135426-L-3704573 2026-10-27 (merge of deliver/J2/Sheaf.Paper.NativeWeilTensorRingedBridge)
