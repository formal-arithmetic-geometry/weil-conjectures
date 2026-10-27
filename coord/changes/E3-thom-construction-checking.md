# AlgebraicGeometry.ProEtale.AffineZeroPurity.target, product, supportedClass, closedSingleIso and thom

## Reason

Profiling found repeated expensive kernel comparisons of concrete derived-category
structures. The target now uses the same named canonical monoidal instance as
supportedCup; this is definitionally the original derived tensor. Named generic
functions form the same List.rec, endpoint transports, supported composite,
closed-single comparison and exceptional adjunct before coefficient specialization.
Local irreducibility of comparisonUpperStar and lowerStar limits elaborator
expansion inside this file. Existing irreducible attributes remain.

Every body is a complete construction, with no data chosen from mere existence.
The only chosen isomorphism remains supportIso, determined uniquely over the tower
by supportIso_existsUnique. No existing signature, public import, mathematical
statement or target meaning changes. The adopted source tree is untouched.

## Old

```lean
abbrev target (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) (c : ℕ) : D P n X :=
  (AffineSpacePurity.action
    ((AffineSpacePurity.tensor (setting P n).Coefficient X).flip.obj
      (AffineSpacePurity.shiftedLine (setting P n) X)) c).obj (unit P n X)
```

```lean
def product (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) : (is : List (Fin c)) →
    classSource P n B c is ⟶ target P n (iteratedAffineLine B c) is.length :=
  List.rec (motive := fun is : List (Fin c) ↦
    classSource P n B c is ⟶ target P n (iteratedAffineLine B c) is.length)
    (eqToHom (classSource_nil P n B c) ≫
      (cupSingle (setting P n) (iteratedAffineLine B c)).map
        ((lowerStarId (ModuleCat.{u + 1} (setting P n).Coefficient)
          (iteratedAffineLine B c)).hom.app
            ((setting P n).constant (iteratedAffineLine B c))))
    (fun i is previous ↦ eqToHom (classSource_cons P n B c i is) ≫
      cupZero (setting P n) (AffineSpacePurity.towerBase aB c)
        (supportMap B c is) (inclusion B c i)
        ⟨target P n (iteratedAffineLine B c) is.length,
          target_plus P n _ (AffineSpacePurity.towerBase aB c) is.length⟩
        ⟨AffineSpacePurity.shiftedLine (setting P n) (iteratedAffineLine B c),
          boundary_plus P n _⟩
        (eqToHom (classSource_eq P n B c is).symm ≫ previous)
        (boundary P n B aB c i) ≫
      eqToHom (target_succ P n (iteratedAffineLine B c) is.length))
```

```lean
def supportedClass (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B c) c :=
  (cupSingle (setting P n) (iteratedAffineLine B c)).map
      ((setting P n).functorialCupSupportMap true (zero B c)
        (supportMap B c (List.finRange c)) (supportIso B c).hom
        (supportIso_existsUnique B c).exists.choose_spec) ≫
    eqToHom (classSource_eq P n B c (List.finRange c)).symm ≫
    product P n B aB c (List.finRange c) ≫
    eqToHom (congrArg (target P n (iteratedAffineLine B c)) (@List.length_finRange c))
```

```lean
def closedSingleIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i)]
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) i).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj M) :=
  (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
      (ModuleCat.{u + 1} A) i).app ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory.app
      ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
    ((lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategorySingleFunctor 0).app M
```

```lean
def thom (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    unit P n B ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (zero B c)).obj (target P n (iteratedAffineLine B c) c) :=
  letI := zero_exact P n B aB c
  letI : IsNoetherian (iteratedAffineLine B c) :=
    AffineSpacePurity.tower_noetherian (setting P n) B aB c
  rightDerivedUpperShriekHomEquiv (K := unit P n B)
    (L := target P n (iteratedAffineLine B c) c) (zero B c) (unit_origin P n B)
    (target_plus P n (iteratedAffineLine B c) (AffineSpacePurity.towerBase aB c) c)
    ((closedSingleIso (setting P n).Coefficient (zero B c)
      ((setting P n).constant B)).hom ≫ supportedClass P n B aB c)
```

## New

```lean
def coordinateProductFold {c : ℕ} {C : Type (u + 2)} [Category.{u + 1} C]
    (S : List (Fin c) → C) (T : ℕ → C)
    (empty : S [] ⟶ T 0)
    (step : ∀ i is, (S is ⟶ T is.length) → (S (i :: is) ⟶ T (i :: is).length)) :
    ∀ is, S is ⟶ T is.length :=
  List.rec empty step
```

```lean
def coordinateProductTransport {C : Type (u + 2)} [Category.{u + 1} C] {W X Y Z : C}
    (a : W = X) (f : X ⟶ Y) (b : Y = Z) : W ⟶ Z :=
  eqToHom a ≫ f ≫ eqToHom b
```

```lean
def coordinateProductStart {C : Type (u + 2)} [Category.{u + 1} C] {W X Y : C}
    (a : W = X) (f : X ⟶ Y) : W ⟶ Y := eqToHom a ≫ f
```

```lean
def coordinateSupportedCompose {C : Type (u + 2)} [Category.{u + 1} C] {W X Y Z U : C}
    (f : W ⟶ X) (e : X = Y) (g : Y ⟶ Z) (h : Z = U) : W ⟶ U :=
  f ≫ eqToHom e ≫ g ≫ eqToHom h
```

```lean
def closedSingleComparison {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{u + 1} C]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : DerivedCategory C ⥤ DerivedCategory D) (e : G ≅ F.rightDerivedFunctor)
    (M : C) : G.obj ((DerivedCategory.singleFunctor C 0).obj M) ≅
      (DerivedCategory.singleFunctor D 0).obj (F.obj M) :=
  e.app ((DerivedCategory.singleFunctor C 0).obj M) ≪≫
    F.rightDerivedFunctorIsoMapDerivedCategory.app
      ((DerivedCategory.singleFunctor C 0).obj M) ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app M
```

```lean
def coordinateThomAdjunct (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [HasCompactification i]
    [Etale.HasBoundedBelowUpperShriek A i]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (hM : DerivedCategory.plusEtaleOrigin A Z K)
    (hL : DerivedCategory.TStructure.t.plus L)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (e : (rightDerivedLowerShriek A i).obj
      K ≅ N) (a : N ⟶ L) :
    K ⟶ (rightDerivedUpperShriek A i).obj L :=
  rightDerivedUpperShriekHomEquiv (K := K)
    (L := L) i hM hL (e.hom ≫ a)
```

```lean
abbrev target (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) (c : ℕ) : D P n X :=
  (AffineSpacePurity.action
    ((@curriedTensor (D P n X) _ (cupMonoidal (setting P n) X)).flip.obj
      (AffineSpacePurity.shiftedLine (setting P n) X)) c).obj (unit P n X)
```

```lean
def product (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) : (is : List (Fin c)) →
    classSource P n B c is ⟶ target P n (iteratedAffineLine B c) is.length :=
  coordinateProductFold (classSource P n B c) (target P n (iteratedAffineLine B c))
    (coordinateProductStart (classSource_nil P n B c)
      ((cupSingle (setting P n) (iteratedAffineLine B c)).map
        ((lowerStarId (ModuleCat.{u + 1} (setting P n).Coefficient)
          (iteratedAffineLine B c)).hom.app
            ((setting P n).constant (iteratedAffineLine B c)))))
    (fun i is previous ↦ coordinateProductTransport (classSource_cons P n B c i is)
      (cupZero (setting P n) (AffineSpacePurity.towerBase aB c)
        (supportMap B c is) (inclusion B c i)
        ⟨target P n (iteratedAffineLine B c) is.length,
          target_plus P n _ (AffineSpacePurity.towerBase aB c) is.length⟩
        ⟨AffineSpacePurity.shiftedLine (setting P n) (iteratedAffineLine B c),
          boundary_plus P n _⟩
        (coordinateProductStart (classSource_eq P n B c is).symm previous)
        (boundary P n B aB c i))
      (target_succ P n (iteratedAffineLine B c) is.length))
```

```lean
def supportedClass (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B c) c :=
  coordinateSupportedCompose ((cupSingle (setting P n) (iteratedAffineLine B c)).map
      ((setting P n).functorialCupSupportMap true (zero B c)
        (supportMap B c (List.finRange c)) (supportIso B c).hom
        (supportIso_existsUnique B c).exists.choose_spec))
    (classSource_eq P n B c (List.finRange c)).symm
    (product P n B aB c (List.finRange c))
    (congrArg (target P n (iteratedAffineLine B c)) (@List.length_finRange c))
```

```lean
def closedSingleIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i)]
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) i).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj M) :=
  closedSingleComparison (lowerStar (ModuleCat.{u + 1} A) i) _
    (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
      (ModuleCat.{u + 1} A) i) M
```

```lean
def thom (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    unit P n B ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (zero B c)).obj (target P n (iteratedAffineLine B c) c) :=
  letI := zero_exact P n B aB c
  letI : IsNoetherian (iteratedAffineLine B c) :=
    AffineSpacePurity.tower_noetherian (setting P n) B aB c
  coordinateThomAdjunct (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)
      (unit P n B) (target P n (iteratedAffineLine B c) c)
      (unit_origin P n B)
      (target_plus P n (iteratedAffineLine B c) (AffineSpacePurity.towerBase aB c) c) _
      (closedSingleIso (setting P n).Coefficient (zero B c) ((setting P n).constant B))
      (supportedClass P n B aB c)
```

## Users

The direct callers retain the same arguments, endpoints and canonical maps.
The generic functions unfold to the original recursion and composites. The target's
named monoidal instance unfolds to the same canonical derived tensor; no coefficient,
shift, tensor order or degree changes. No consumer needs adaptation.

The table lists the complete current downstream import closure, as returned by
tools/downstream.py. Holders are read from the current claim records.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AffineSpaceThomMap | E3 | Own construction; same canonical data. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | D4 | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | C6 | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | Y8 | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | K6 | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | F1 | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | S3 | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same signatures and definitionally identical maps; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same signatures and definitionally identical maps; no adaptation. |

## Status

landed 20261025T204524-L-2968039 2026-10-25 (merge of deliver/E3/Sheaf.Paper.AffineSpaceThomMap)
