# Canonical proper-etale-origin scalar comparison data

## Reason

Extract the eight existing supporting constructions into
`Sheaf.Paper.ProperEtaleOriginScalarData`, publicly reexported by the original item.
This lets the separate qcqs projection-square lemma use the canonical constructions
without an import cycle through the proper-isomorphism theorem. This extraction is
unrelated to compilation time: the original and the extracted files compile below
the single-file limit. Every existing construction has the same signature,
visibility, attributes and defining expression. No source-library file is changed.

## Old

The following declarations were in
`Sheaf.Paper.ProperEtaleOriginScalarIsomorphism`:

```lean
/-- The identity-on-sections change from the counit-adjoint coefficient map to
its original constant-section map. Source: Stacks 03D1 and 0H7J
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginPushIso (A : Type u) [CommRing A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    directImageConstantPush A p ≅ Scheme.proEtaleConstantDerivedDirectImage p A :=
  Functor.rightDerivedFunctorNatIso
    (SheafOfModules.pushforwardCongr
      (congrArg (fun g : Scheme.proEtaleConstantRing Y A ⟶
          (Scheme.proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj
            (Scheme.proEtaleConstantRing Z A) ↦
        (sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g)
        ((Scheme.proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
          |>.apply_symm_apply (Scheme.proEtaleCoefficientDirectImageMap p A))))

/-- Restriction commutes with the specified comparison inverse image, with the
identity-on-sections realization normalization. Source: Stacks 03D2 and 00YV
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginRestrictionIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    finiteCoefficientIntrinsicDerivedComparison T B ⋙
        (scalarMateRestriction φ T).mapDerivedCategory ≅
      Sheaf.derivedRestrictScalars T.smallEtaleTopology (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
        finiteCoefficientIntrinsicDerivedComparison T A :=
  Functor.isoWhiskerRight (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso B T) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategorySquareIso (Scheme.sfRealizationRestriction T φ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (pbcDerivedComparisonRestrict T
        (R := ULift.{u + 1, u} A) (S := ULift.{u + 1, u} B)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A T).symm

/-- Ordinary etale tensor with the constant A-module B in degree zero.
This uses the existing tensor and coefficient, without changing either.
Source: Stacks 0F0G (blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
def properOriginEtaleTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule A T) : Etale.DerivedCategoryModule A T :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj M).obj
    (Etale.scalarCoefficient φ T)

/-- Image of the canonical scalar/tensor component under a functor. Stating this
at general coefficients keeps specialization to lifted rings small.
Source: Stacks 06YY (blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginScalarTensorImage
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) {C : Type v} [Category.{w} C]
    (F : Etale.DerivedCategoryModule A T ⥤ C)
    (M : Etale.DerivedCategoryModule A T) {X : C}
    (e : F.obj ((Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).obj
      ((Etale.scalarExtension φ T).obj M)) ≅ X) :=
  F.mapIso ((Etale.scalarTensorIso φ T).app M).symm ≪≫ e

/-- The canonical comparison F(M tensor B) = U S F(M). It is the tensor
comparison specialized to the constant coefficient B, expressed using the
representative-normalized scalar/tensor identifications. All its factors are
published normalized comparisons, including the scalar-adjunction mate.
Source: Stacks 06YY, 07A4 and 0D6D
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginTensorIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T) :=
  let e₂ := (properOriginRestrictionIso φ T).symm.app
    ((Etale.scalarExtension (A := ULift.{u + 1, u} A) (B := ULift.{u + 1, u} B)
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) T).obj M)
  let e₃ := (scalarMateRestriction φ T).mapDerivedCategory.mapIso
    ((Scheme.FiniteCompactScalar.siteScalarIso φ T).symm.app M)
  properOriginScalarTensorImage
    (A := ULift.{u + 1, u} A) (B := ULift.{u + 1, u} B)
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) T
    (finiteCoefficientIntrinsicDerivedComparison T A) M (e₂ ≪≫ e₃)

/-- The fixed counit mate on D+, included in the unbounded categories by the
standard endpoint compatibilities. Source: Stacks 09A6
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginFixedMateIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj K.obj) ≅
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj K.obj) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.app
        K).symm ≪≫
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility.app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.obj K)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      ((@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A p)
        (isIso_fixedComparisonDirectImageMatePlus A p)).app K) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj K) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlusCompatibility.app K)

/-- The same specified mate in intrinsic constant-ring modules. The additional
factors only change coefficient presentations and their section-normalized direct
images; they do not choose another mate. Source: Stacks 09A6 and 00YV
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginMateIso (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (finiteCoefficientIntrinsicDerivedComparison Y A).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          K.obj) ≅
      (directImageConstantPush A p).obj
        ((finiteCoefficientIntrinsicDerivedComparison Z A).obj K.obj) :=
  (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Y).app _ ≪≫
    (Scheme.sfIntrinsicDerivedEquivalence Y A).functor.mapIso
      (properOriginFixedMateIso (ULift.{u + 1, u} A) p K) ≪≫
    (Scheme.sfIntrinsicDerivedDirectImageComparison p A).symm.app _ ≪≫
    (Scheme.proEtaleConstantDerivedDirectImage p A).mapIso
      ((Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Z).app K.obj).symm ≪≫
    (properOriginPushIso A p).symm.app _

/-- The actual etale projection arrow followed only by the canonical identification
p*B_Y = B_Z. Source: Stacks 0B56 and 0F0G
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginEtaleProjection
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (M : Etale.DerivedCategoryModule A Z) :
    properOriginEtaleTensor φ Y
        ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj M) ⟶
      (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj
        (properOriginEtaleTensor φ Z M) :=
  ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app M).app
      (Etale.scalarCoefficient φ Y) ≫
    (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).obj M).map
        (Etale.scalarCoefficientPullbackIso φ p).hom)
```

## New

The identical declarations below are in
`Sheaf.Paper.ProperEtaleOriginScalarData`. The new module docstring attaches the extraction to its data node;
existing declaration docstrings are retained verbatim. The original module publicly imports this module, so existing importers
still see the same declarations and their original public-import closure.

```lean
/-- The identity-on-sections change from the counit-adjoint coefficient map to
its original constant-section map. Source: Stacks 03D1 and 0H7J
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginPushIso (A : Type u) [CommRing A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    directImageConstantPush A p ≅ Scheme.proEtaleConstantDerivedDirectImage p A :=
  Functor.rightDerivedFunctorNatIso
    (SheafOfModules.pushforwardCongr
      (congrArg (fun g : Scheme.proEtaleConstantRing Y A ⟶
          (Scheme.proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj
            (Scheme.proEtaleConstantRing Z A) ↦
        (sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g)
        ((Scheme.proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
          |>.apply_symm_apply (Scheme.proEtaleCoefficientDirectImageMap p A))))

/-- Restriction commutes with the specified comparison inverse image, with the
identity-on-sections realization normalization. Source: Stacks 03D2 and 00YV
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginRestrictionIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    finiteCoefficientIntrinsicDerivedComparison T B ⋙
        (scalarMateRestriction φ T).mapDerivedCategory ≅
      Sheaf.derivedRestrictScalars T.smallEtaleTopology (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
        finiteCoefficientIntrinsicDerivedComparison T A :=
  Functor.isoWhiskerRight (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso B T) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategorySquareIso (Scheme.sfRealizationRestriction T φ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (pbcDerivedComparisonRestrict T
        (R := ULift.{u + 1, u} A) (S := ULift.{u + 1, u} B)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A T).symm

/-- Ordinary etale tensor with the constant A-module B in degree zero.
This uses the existing tensor and coefficient, without changing either.
Source: Stacks 0F0G (blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
def properOriginEtaleTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule A T) : Etale.DerivedCategoryModule A T :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj M).obj
    (Etale.scalarCoefficient φ T)

/-- Image of the canonical scalar/tensor component under a functor. Stating this
at general coefficients keeps specialization to lifted rings small.
Source: Stacks 06YY (blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginScalarTensorImage
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) {C : Type v} [Category.{w} C]
    (F : Etale.DerivedCategoryModule A T ⥤ C)
    (M : Etale.DerivedCategoryModule A T) {X : C}
    (e : F.obj ((Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).obj
      ((Etale.scalarExtension φ T).obj M)) ≅ X) :=
  F.mapIso ((Etale.scalarTensorIso φ T).app M).symm ≪≫ e

/-- The canonical comparison F(M tensor B) = U S F(M). It is the tensor
comparison specialized to the constant coefficient B, expressed using the
representative-normalized scalar/tensor identifications. All its factors are
published normalized comparisons, including the scalar-adjunction mate.
Source: Stacks 06YY, 07A4 and 0D6D
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginTensorIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T) :=
  let e₂ := (properOriginRestrictionIso φ T).symm.app
    ((Etale.scalarExtension (A := ULift.{u + 1, u} A) (B := ULift.{u + 1, u} B)
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) T).obj M)
  let e₃ := (scalarMateRestriction φ T).mapDerivedCategory.mapIso
    ((Scheme.FiniteCompactScalar.siteScalarIso φ T).symm.app M)
  properOriginScalarTensorImage
    (A := ULift.{u + 1, u} A) (B := ULift.{u + 1, u} B)
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) T
    (finiteCoefficientIntrinsicDerivedComparison T A) M (e₂ ≪≫ e₃)

/-- The fixed counit mate on D+, included in the unbounded categories by the
standard endpoint compatibilities. Source: Stacks 09A6
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginFixedMateIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj K.obj) ≅
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj K.obj) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.app
        K).symm ≪≫
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility.app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.obj K)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      ((@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A p)
        (isIso_fixedComparisonDirectImageMatePlus A p)).app K) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj K) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlusCompatibility.app K)

/-- The same specified mate in intrinsic constant-ring modules. The additional
factors only change coefficient presentations and their section-normalized direct
images; they do not choose another mate. Source: Stacks 09A6 and 00YV
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginMateIso (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (finiteCoefficientIntrinsicDerivedComparison Y A).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          K.obj) ≅
      (directImageConstantPush A p).obj
        ((finiteCoefficientIntrinsicDerivedComparison Z A).obj K.obj) :=
  (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Y).app _ ≪≫
    (Scheme.sfIntrinsicDerivedEquivalence Y A).functor.mapIso
      (properOriginFixedMateIso (ULift.{u + 1, u} A) p K) ≪≫
    (Scheme.sfIntrinsicDerivedDirectImageComparison p A).symm.app _ ≪≫
    (Scheme.proEtaleConstantDerivedDirectImage p A).mapIso
      ((Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Z).app K.obj).symm ≪≫
    (properOriginPushIso A p).symm.app _

/-- The actual etale projection arrow followed only by the canonical identification
p*B_Y = B_Z. Source: Stacks 0B56 and 0F0G
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism). -/
@[irreducible] def properOriginEtaleProjection
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (M : Etale.DerivedCategoryModule A Z) :
    properOriginEtaleTensor φ Y
        ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj M) ⟶
      (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj
        (properOriginEtaleTensor φ Z M) :=
  ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app M).app
      (Etale.scalarCoefficient φ Y) ≫
    (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).obj M).map
        (Etale.scalarCoefficientPullbackIso φ p).hom)
```

## Users

`python3 tools/downstream.py Sheaf.Paper.ProperEtaleOriginScalarIsomorphism --uses`
was run with all eight names. It found zero downstream Lean modules; every name
occurred only in the original item. A search of DAG parents found the unfinished
compact-support coefficient-change parent. Its dependency and this item's public
statement remain unchanged. No quarantined parent is withdrawn or edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperEtaleOriginScalarIsomorphism | W6 | Publicly reexports the identical constructions; proves the original theorem from the qcqs square and proper torsion projection. |
| Sheaf.Paper.ProperEtaleOriginScalarData | W6 packet | New home of the identical eight definitions, with their existing public imports. |
| Sheaf.Paper.EtaleOriginScalarProjectionSquare | W6 packet | New genuine compatibility lemma; uses the data without importing the proper theorem. |

The extraction changes no mathematical definition or target meaning. No forced
adaptation of another group's module is included.

## Status

landed 20261021T152415-L-1937288 2026-10-21 (merge of deliver/W6/Sheaf.Paper.ProperEtaleOriginScalarIsomorphism)
