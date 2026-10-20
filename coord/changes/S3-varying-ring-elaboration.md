# AlgebraicGeometry.ProEtale.VaryingRing.eval

## Reason

Preserve the concrete coefficient constructions and all public mathematical statements,
while avoiding repeated inference of functors in derived comparisons. Explicit result
types on evaluation and its ordinary comparisons are precisely the types formerly
inferred. The composition and evaluation comparisons now give their existing implicit
functor arguments explicitly. These are definitionally identical constructions.
The private AsSmall transport proof is generalized over abstract ring sheaves to avoid
unfolding constant-sheaf data. All added imports are proof-only.

Local irreducibility attributes keep chosen adjoints and derived functor constructions
abstract during elaboration. These local attributes do not alter imported declarations
or affect downstream elaboration. No definition is replaced by arbitrary chosen data.

## Old

There were no local transparency attributes on the three functor constructions.

```lean
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : G R φ f ⊣ P R φ f :=
  (moduleAdj R φ f).mapDerivedCategoryRightDerivedAdjunction
```

```lean
def moduleGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull R φ (f ≫ g) ≅ pull R φ g ⋙ pull R φ f :=
  (Adjunction.leftAdjointCompIso (moduleAdj R φ g) (moduleAdj R φ f)
    (moduleAdj R φ (f ≫ g)) (modulePComp R φ f g)).symm
```

```lean
def gComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G R φ (f ≫ g) ≅ G R φ g ⋙ G R φ f :=
  Functor.mapDerivedCategoryNatIso (moduleGComp R φ f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
```

```lean
def pComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P R φ f ⋙ P R φ g ≅ P R φ (f ≫ g) :=
  conjugateIsoEquiv ((adj R φ g).comp (adj R φ f)) (adj R φ (f ≫ g)) (gComp R φ f g)
```

```lean
def gId (X : Scheme.{u}) : G R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  Functor.mapDerivedCategoryNatIso
    (Adjunction.leftAdjointIdIso (moduleAdj R φ (𝟙 X)) (modulePId R φ X)) ≪≫
      Functor.mapDerivedCategoryIdIso _
```

```lean
def pId (X : Scheme.{u}) : P R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  (conjugateIsoEquiv Adjunction.id (adj R φ (𝟙 X)) (gId R φ X)).symm
```

```lean
def jAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : J R φ j ⊣ G R φ j :=
  Adjunction.ofNatIsoRight ((moduleJAdj R φ j).mapDerivedCategoryRightDerivedAdjunction)
    (pull R φ j).rightDerivedFunctorIsoMapDerivedCategory
```

```lean
def moduleJComp {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    extension R φ i ⋙ extension R φ j ≅ extension R φ (i ≫ j) :=
  Adjunction.leftAdjointCompIso (moduleJAdj R φ i) (moduleJAdj R φ j)
    (moduleJAdj R φ (i ≫ j)) (moduleGComp R φ i j).symm
```

```lean
def jComp {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] : J R φ i ⋙ J R φ j ≅ J R φ (i ≫ j) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleJComp R φ i j)
```

```lean
def jId (X : Scheme.{u}) : J R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  Adjunction.leftAdjointIdIso (jAdj R φ (𝟙 X)) (gId R φ X)
```

```lean
abbrev eval (X : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X) n
```

```lean
def moduleEvalP {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (moduleEvalP_existsUnique R φ f n).choose
```

```lean
def moduleEvalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (moduleEvalG_existsUnique R φ f n).choose
```

```lean
def evalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    G R φ f ⋙ ev R φ X n ≅
      ev R φ Y n ⋙ (StrictTower.modulePullback (R n) f).mapDerivedCategory :=
  letI : (StrictTower.modulePullback (R n) f).Additive :=
    StrictTower.modulePullback_additive (R n) f
  letI : PreservesFiniteLimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteLimits (R n) f
  letI : PreservesFiniteColimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteColimits (R n) f
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleEvalG R φ f n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
```

```lean
def levelAdj {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
    (coefficients R X n)
      (StrictTower.constantRingIso (R n) f)).mapDerivedCategoryRightDerivedAdjunction
```

```lean
def evalPMate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    P R φ f ⋙ ev R φ Y n ⟶
      ev R φ X n ⋙ (StrictTower.moduleDirectImage (R n) f).rightDerivedFunctor :=
  mateEquiv (adj R φ f) (levelAdj R f n) (evalG R φ f n).inv
```

```lean
def levelJAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  Adjunction.ofNatIsoRight
    ((StrictTower.moduleJAdj (R n) j).mapDerivedCategoryRightDerivedAdjunction)
      (StrictTower.modulePullback (R n) j).rightDerivedFunctorIsoMapDerivedCategory
```

```lean
def evalJInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    ev R φ U n ⋙ (StrictTower.moduleJ (R n) j).mapDerivedCategory ⟶
      J R φ j ⋙ ev R φ X n :=
  (mateEquiv (jAdj R φ j) (levelJAdj R j n)).symm (evalG R φ j n).hom
```

## New

```lean
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor
```

```lean
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : G R φ f ⊣ P R φ f :=
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
    (L := pull R φ f) (R := push R φ f) (moduleAdj R φ f)
```

```lean
def moduleGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull R φ (f ≫ g) ≅ pull R φ g ⋙ pull R φ f :=
  (Adjunction.leftAdjointCompIso
    (F₀₁ := pull R φ g) (F₁₂ := pull R φ f) (F₀₂ := pull R φ (f ≫ g))
    (G₁₀ := push R φ g) (G₂₁ := push R φ f) (G₂₀ := push R φ (f ≫ g))
    (moduleAdj R φ g) (moduleAdj R φ f)
    (moduleAdj R φ (f ≫ g)) (modulePComp R φ f g)).symm
```

```lean
def gComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G R φ (f ≫ g) ≅ G R φ g ⋙ G R φ f :=
  Functor.mapDerivedCategoryNatIso (moduleGComp R φ f g) ≪≫
    Functor.mapDerivedCategoryCompIso (pull R φ g) (pull R φ f)
```

```lean
def pComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P R φ f ⋙ P R φ g ≅ P R φ (f ≫ g) :=
  conjugateIsoEquiv (L₁ := G R φ g ⋙ G R φ f) (R₁ := P R φ f ⋙ P R φ g)
    (L₂ := G R φ (f ≫ g)) (R₂ := P R φ (f ≫ g))
    ((adj R φ g).comp (adj R φ f)) (adj R φ (f ≫ g)) (gComp R φ f g)
```

```lean
def gId (X : Scheme.{u}) : G R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  Functor.mapDerivedCategoryNatIso
    (Adjunction.leftAdjointIdIso (F := pull R φ (𝟙 X)) (G := push R φ (𝟙 X))
      (moduleAdj R φ (𝟙 X)) (modulePId R φ X)) ≪≫
      Functor.mapDerivedCategoryIdIso _
```

```lean
def pId (X : Scheme.{u}) : P R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  (conjugateIsoEquiv (L₁ := 𝟭 (Derived R φ X)) (R₁ := 𝟭 (Derived R φ X))
    (L₂ := G R φ (𝟙 X)) (R₂ := P R φ (𝟙 X))
    Adjunction.id (adj R φ (𝟙 X)) (gId R φ X)).symm
```

```lean
def jAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : J R φ j ⊣ G R φ j :=
  Adjunction.ofNatIsoRight (F := (pull R φ j).rightDerivedFunctor) (G := G R φ j)
    (H := J R φ j)
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (L := extension R φ j) (R := pull R φ j) (moduleJAdj R φ j))
    (pull R φ j).rightDerivedFunctorIsoMapDerivedCategory
```

```lean
def moduleJComp {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    extension R φ i ⋙ extension R φ j ≅ extension R φ (i ≫ j) :=
  Adjunction.leftAdjointCompIso
    (F₀₁ := extension R φ i) (F₁₂ := extension R φ j) (F₀₂ := extension R φ (i ≫ j))
    (G₁₀ := pull R φ i) (G₂₁ := pull R φ j) (G₂₀ := pull R φ (i ≫ j))
    (moduleJAdj R φ i) (moduleJAdj R φ j)
    (moduleJAdj R φ (i ≫ j)) (moduleGComp R φ i j).symm
```

```lean
def jComp {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] : J R φ i ⋙ J R φ j ≅ J R φ (i ≫ j) :=
  (Functor.mapDerivedCategoryCompIso (extension R φ i) (extension R φ j)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleJComp R φ i j)
```

```lean
def jId (X : Scheme.{u}) : J R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  Adjunction.leftAdjointIdIso (F := J R φ (𝟙 X)) (G := G R φ (𝟙 X))
    (jAdj R φ (𝟙 X)) (gId R φ X)
```

```lean
abbrev eval (X : Scheme.{u}) (n : ℕ) :
    Modules R φ X ⥤ StrictTower.Modules (R n) X :=
  SemilinearSections.evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X) n
```

```lean
def moduleEvalP {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    push R φ f ⋙ eval R φ Y n ≅
      eval R φ X n ⋙ StrictTower.moduleDirectImage (R n) f :=
  (moduleEvalP_existsUnique R φ f n).choose
```

```lean
def moduleEvalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pull R φ f ⋙ eval R φ X n ≅
      eval R φ Y n ⋙ StrictTower.modulePullback (R n) f :=
  (moduleEvalG_existsUnique R φ f n).choose
```

```lean
def evalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    G R φ f ⋙ ev R φ X n ≅
      ev R φ Y n ⋙ (StrictTower.modulePullback (R n) f).mapDerivedCategory :=
  letI : (StrictTower.modulePullback (R n) f).Additive :=
    StrictTower.modulePullback_additive (R n) f
  letI : PreservesFiniteLimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteLimits (R n) f
  letI : PreservesFiniteColimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteColimits (R n) f
  (Functor.mapDerivedCategoryCompIso (pull R φ f) (eval R φ X n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleEvalG R φ f n) ≪≫
      Functor.mapDerivedCategoryCompIso (eval R φ Y n)
        (StrictTower.modulePullback (R n) f)
```

```lean
def levelAdj {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
    (L := Scheme.proEtaleRingModulePullback f (coefficients R Y n) (coefficients R X n)
      (StrictTower.constantRingIso (R n) f))
    (R := Scheme.proEtaleRingModuleDirectImage f (coefficients R Y n) (coefficients R X n)
      (StrictTower.constantRingIso (R n) f))
    (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n) (coefficients R X n)
      (StrictTower.constantRingIso (R n) f))
```

```lean
def evalPMate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    P R φ f ⋙ ev R φ Y n ⟶
      ev R φ X n ⋙ (StrictTower.moduleDirectImage (R n) f).rightDerivedFunctor :=
  mateEquiv (L₁ := G R φ f) (R₁ := P R φ f)
    (L₂ := (StrictTower.modulePullback (R n) f).mapDerivedCategory)
    (R₂ := (StrictTower.moduleDirectImage (R n) f).rightDerivedFunctor)
    (G := ev R φ Y n) (H := ev R φ X n)
    (adj R φ f) (levelAdj R f n) (evalG R φ f n).inv
```

```lean
def levelJAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  Adjunction.ofNatIsoRight
    (F := (StrictTower.modulePullback (R n) j).rightDerivedFunctor)
    (G := (StrictTower.modulePullback (R n) j).mapDerivedCategory)
    (H := (StrictTower.moduleJ (R n) j).mapDerivedCategory)
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (L := StrictTower.moduleJ (R n) j) (R := StrictTower.modulePullback (R n) j)
      (StrictTower.moduleJAdj (R n) j))
      (StrictTower.modulePullback (R n) j).rightDerivedFunctorIsoMapDerivedCategory
```

```lean
def evalJInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    ev R φ U n ⋙ (StrictTower.moduleJ (R n) j).mapDerivedCategory ⟶
      J R φ j ⋙ ev R φ X n :=
  (mateEquiv (L₁ := J R φ j) (R₁ := G R φ j)
    (L₂ := (StrictTower.moduleJ (R n) j).mapDerivedCategory)
    (R₂ := (StrictTower.modulePullback (R n) j).mapDerivedCategory)
    (G := ev R φ U n) (H := ev R φ X n)
    (jAdj R φ j) (levelJAdj R j n)).symm (evalG R φ j n).hom
```

Reviewer correction (2026-10-21): the explicit functors of levelAdj are the
Scheme.proEtaleRingModulePullback/DirectImage functors of proEtaleRingModuleAdjunction, the type
levelAdj had before. Naming the StrictTower.modulePullback/moduleDirectImage wrappers (plain defs)
changed the stored type and broke instance search in VaryingRingProperOpenArrows (Faithful of
the right derived direct image, line 336).

## Users

The source scan lists the transitive consumers below. The two direct importers are
VaryingRingProperOpenArrows and FiniteSystemPullbackCoherence. The mathematical
meaning of every declaration is unchanged, including the unit normalization and
the section formulas. No consumer requires a signature or proof adaptation. In
particular the explicit unfoldings of pComp and pId in VaryingRingProperOpenPasting
still expose the same conjugateIsoEquiv expressions.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.VaryingRingOperations | S3 | proofs and elaboration annotations |
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.DeligneLaumon.QbarCurveDuality | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.A1LisseSectionEvaluation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.A1QbarOpenClosedCohomology | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicCompactificationSectionRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicHeartIntrinsicFibres | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicLisseCohomologyCalculus | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicLocalCharacteristicFactor | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicMiddleExtensionConstructible | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicPunctualWeights | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicPurityExceptionalReduction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicPurityFiniteTensor | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicPurityObjects | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicPurityRootComparisons | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicPuritySourceReduction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicPurityTwistReduction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicSectionCanonicalModels | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicSectionClosedSupport | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AdmissibleVerdierExchange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AffineCurveHcZero | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AffineLineInvariance | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AffineSpaceRationalInduction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ArithmeticRoots | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.BasicOperationsCoefficientReduction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.BoundaryHomVanishing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.BoundaryOrdinaryImages | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.BrownExceptionalAdjoint | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ClosedSupportedCupVanishing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CoefficientTowerGeometricComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CoherentRationalPullbackIdentity | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CommonAdicCompactificationSectionData | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CommonAdicOpenSectionData | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CommonAdicSectionData | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CommonStageCompactWeilCohomology | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CommonStageFourierTransform | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CommonStagePullbackIdentity | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CommonStageWeilFourierTransform | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CommonStageWeilLinearDual | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CommonStageWeilShriek | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompactSupportLerayFiltration | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompactSupportPerfectness | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompactSupportProjectionFormula | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompactSupportUniformTorBound | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompactificationCoherenceCocycle | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompactificationLocalizing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompactificationRefinementIdentity | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompactificationRefinementLocalizing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompletedOperationTowerSubstitution | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompletedPullbackTensorComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CompletedTensorHomTranspose | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ConnectedConstantH0 | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ConstantExtensionCompactComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ConstantWeilStructure | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ConstructibleProjectionMates | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ConstructiblePullbackTExact | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ConstructibleTruncations | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ContinuousRationalDerivedRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CoprojectionCompositionMate | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CurveIntermediateExtension | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.CurveMiddleExtensionUpper | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DegreeZeroCompactSupportSections | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DerivedPullbackTensorIso | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DerivedTruncationCoproducts | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DeterminantalWeightCoefficientField | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DiagonalTowerTraceModels | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DiagonalTowerTracePresentations | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DlConstantFieldCharts | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DlConstructibleFibresExact | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DualStalkFrobenius | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.DualizingObjectPurity | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.EtaleLocallyClosedShriek | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.EtaleRhoMonoidalMate | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ExceptionalFiniteRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ExceptionalInverseImageExistence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ExceptionalProEtaleRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ExceptionalSiteRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ExplicitExceptionalPreservation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ExtensionByZeroPunctual | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FdCoefficientComparisonSystem | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FieldShriekCompositionQcqs | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FieldShriekLowerBound | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FieldStageOrdinaryRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FieldTorAmplitude | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FieldWeilShriekShiftData | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FilteredCoefficientTensorBounds | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteAdicImageNormalization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteAdicOpenSectionData | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteAdicProperSectionData | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteAdjointMateCompatibility | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteBoundaryWeights | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteClosedShriek | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteCoefficientHomChange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteCompactificationWeilExact | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteDncNormalizationReduction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteEtaleDescent | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteExtensionReductionConeBound | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteForwardProductSymmetry | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteFreeCoefficientExtension | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteFreeCompactComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteFreeCompactScalar | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteFreeProjectionExchange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteFreeScalarProjection | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteIndHeartAdjunction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FinitePointInternalHomEvaluation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteProductCompactification | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteProjectionActionLaws | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteProperLocalizing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteReductionAffineOrientation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteReductionChartCalculus | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteReductionComparisons | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteReductionOfPurity | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteReductionRootCharts | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteStructuralMapsCommShift | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteSystemPullbackCoherence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteTorStability | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FiniteWeilIndPushExact | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FixedStalkIdentificationReduction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FourierTraceFormula | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FourierTraceFunctions | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FrobeniusFixesUnitSection | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FrobeniusGeometricExchange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.FrobeniusSquareExchange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.GlobalGeometricFrobenius | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.GlobalVerdierDuality | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.HomFiniteProjective | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ImmersionWeilLocalBehavior | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralCoherenceTower | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralComparisonRealizationModels | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralComparisonSequenceSystems | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralConstructibleReductionFibres | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralDirectImageTower | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralExceptionalInverseImage | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralOpenImageProperFormulas | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralPointTransportTowerPowers | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralPointTransportTowerRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralProperBaseChange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralProperCohomologicalBounds | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralProperDirectSums | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralProperProjectionFormula | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralPullbackComparisonRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralPullbackComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralPullbackReductionCounit | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralPullbackResolutionMatching | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralPullbackSystemComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralTowerInverseImageUnit | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IntegralTowerLimitComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.InterchangeProperPasting | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.InternalAdjunctionPairingChange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.InternalHomPullback | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IsomorphismDerivedPullback | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IteratedWeilCocycle | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.IteratedWeilMap | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.LisseDenseOpenRecovery | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.LisseExtensionInertia | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.LocalFrobeniusConjugacy | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.LocalFrobeniusTrace | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.LocalWeilModelTraceIndependence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.LocalizingLowerShriekComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.MateOpenRestriction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.MiddleExtensionHcZero | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.MiddleExtensionSectionRestriction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ModelCompactComparisonUnit | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.NonrationalCompositionSeed | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.OpenCompactSupportFiniteTor | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.OpenImmersionLocalizing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.OrdinaryCompactCohomology | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PfRefinementCompatibility | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PoincarePointFiniteness | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PointCompletedEvaluation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PointIdentityAdmissibility | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProEtaleProperOpenInterchange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProjectionFiniteReduction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperBaseChangeRational | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperCoincidenceFrobenius | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperCompactCoincidence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperExceptionalRestriction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperHeartBound | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperHeartConstructibleCohomology | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperIndConstructibleUnbounded | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperSectionsSemilinearGerms | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperUnboundedCoproductComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperUnboundedCoproducts | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperUnboundedWindow | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ProperUnboundedWindowIso | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PunctualSpectrumExactFibre | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurAdicReconstruction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityAffineLineOrientation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityAffineLineSupportStalk | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityCompositionCoherence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityCoprojection | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityDiagonalDualizingObject | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityDiagonalSectionPasting | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityDncFamilyIntrinsic | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityGeneralAdmissibility | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityGysinStructure | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityRelativeKummer | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PuritySourceTransports | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.PurityTwistCancellation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.QbarCurveOrdinaryImage | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.QbarPerverseSubcategories | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.QbarPerverseSupportCondition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalCoefficientCategoryComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalDirectImageRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalExceptionalRestriction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalHomScalarTranspose | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalLocalizingProjectionFormula | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalRealizationTensorComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalRestrictionGlue | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalSmoothPurityCanonical | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalStalkExact | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalTensorSymmetry | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.RestrictionLocal | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ScalarExchangeConstituents | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ScalarExtensionTensorUnit | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ScalarExtensionTowerCoherence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SfBidualityClass | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SfCommonStageDirectImage | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SfCommonStageWeilCohomology | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SfProEtaleProjectionFormula | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SfRationalDirectImageAdjunction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SiteComparisonEdgeSection | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SitePerfectCoefficientDual | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SitePerfectDualizableHom | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SitePerfectRationalBidual | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SixFunctorDatum | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SixFunctorDualNotation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SixFunctorOperationDatum | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SixFunctorOperationDatumStages | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SmoothProperPurityHypotheses | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SmoothPullbackSupportDimension | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SmoothPurityMap | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SmoothPurityQbar | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SmoothPurityTowerBound | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SmoothPurityTowerClasses | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SmoothTrace | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SystemClopenTensorCompatibility | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.SystemOperationExchangeRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TateTwistSupportCondition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TensorAdjunctionExchange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TowerClassChern | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TowerClassCoefficients | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TowerClassDiagonal | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TowerClassFinite | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TowerClassFiniteDiagonal | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TowerClassProjective | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TowerClassPullback | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TowerClassReduction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TowerClassSystems | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TowerClassTwisting | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceBaseChangeSecond | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceCohomologicalCorrespondence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceCompactificationCohomology | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceFixedScheme | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceFormulaAdicSystem | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceFormulaCoefficientConventions | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceFormulaDualizingComplex | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TraceGraphCorrespondence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TrfDevissageGeneration | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TrfWitnessedOpenPullback | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TwConventions | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TwFrobeniusAction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.TwistFrobeniusScalar | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.UnboundedBaseChangeExtension | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.VaryingRingGraphSummand | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.VectorBundlePurity | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.VerdierExchange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.WeilCompactSupportCohomology | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.WeilComplexTraceFunction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.WeilConstantExtensionFrobenius | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.WeilFourierPlancherel | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.WeilIndSheafCategory | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.WeilMixedUpperBounds | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.WeilOpenImageDelta | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.WeilPullbackLocalFrobenius | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.WeilShriekShiftCompatibility | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.WfTensorCompletionFrobenius | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ZlFiniteAdicDirectImage | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ZlFrameworkOpenExchange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Paper.ZlShriekComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SecSmoothPurity.MixedBaseChange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SecSmoothPurity.ReductionExceptional | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.AmbientProperOpenPasting | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.CoefQbarVerdier | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.CoefTowerTraceRectification | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.CompactCoefficientComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.CompositionProjectionMate | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FiniteDualizing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FiniteExceptional | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FrobeniusFixedPoints | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FrobeniusPointTransport | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.GeneratorReductionStatement | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralBasicOperationShift | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralComplementFiniteness | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralDualizing | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralOperationShiftData | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralRealizationRecursion | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionLine | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralSystemOperations | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.IntegralVerdier | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.InternalHomPullback | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.OpenAdjunctionShift | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.ProperImageLocalizingProper | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.ProperOpenProjectionMate | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.RationalOperations | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.RationalRetractEvaluation | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.RationalVerdier | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.SmoothPurity.NormalizedWitness | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Targets.AffineSpaceRationalLine | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Targets.PoincareUncurry | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.Targets.SmoothPurityQbar | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.TraceFormula.PointTransportComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | not consulted; unchanged | definitionally identical API; no adaptation |
| Sheaf.ZetaWeil.WeightPurityRoots | not consulted; unchanged | definitionally identical API; no adaptation |
| TargetsCheck | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.PoincareDuality.Poincare | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.PoincareDuality.ProjectionFormula | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.PoincareDuality.Verdier | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.SmoothPurity.Defs | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.TraceFormula.Basic | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.TraceFormula.Slop.Basic | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.TraceFormula.Slop.Correspondence | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.TraceFormula.Slop.Dualizing | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.TraceFormula.Slop.Frobenius | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.TraceFormula.Slop.Main | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.TraceFormula.Slop.Stalk | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.TraceFormula.Statement | not consulted; unchanged | definitionally identical API; no adaptation |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not consulted; unchanged | definitionally identical API; no adaptation |

No target-used definition changes its mathematical meaning. Target statements, public
imports and the unit route are retained. No source-library module is modified.

## Status

landed 20261020T221344-L-4177651 2026-10-20 (merge of deliver/S3/Sheaf.AlgebraicGeometry.VaryingRingOperations)
