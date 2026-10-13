# AlgebraicGeometry.localEvaluationModules and ordinary evaluation constructions

## Reason

The new assembly theorem needs the existing evaluation constructions without importing its
caller. Spelling all constructors inline in its statement hit the 60-second elaboration
limit (a smaller heartbeat budget instead reported a typeclass timeout at mapBifunctor).
Move the existing declarations into BoundedOrdinaryEvaluationAssembly and public
import that module from StrictlyPerfectOrdinaryEvaluation. This creates no duplicate notion,
changes no constructed object, and preserves every original constant name, signature and visibility. The original module exports the same constants through its public
import. The target theorem statement and its meaning stay identical. There is no downstream
adaptation; no existing module other than the assigned item is edited.

Profiling during the second reading identified repeated kernel reduction of the large
`homComplex_exists` specification in `localEvaluationProjection` as the timeout cause.
Replace its body with choice from the already-proved `homComplex_projections_exists`.
That theorem has definitionally the same existential proposition as the old
`Classical.choose_spec` expression. Proof irrelevance therefore makes the selected data
definitionally equal. A scratch Lean equality test against the complete old body is
proved by `rfl`. No arbitrary witness or new mathematical construction is introduced.
The old definition signature and docstring remain unchanged; all other bodies are
relocated verbatim. The assembly imports the projections module publicly for this body.

## Old

In `Sheaf.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation`:

```lean
local instance localEvaluationPreadditive {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    MonoidalPreadditive (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  Classical.choice (SheafOfModules.tensorClosed R).1

/-- The existing module category on the localized site, written in the carrier form
used by internal Hom. This is an abbreviation, not a different module category.
Source: Stacks Project, Tag 08DL
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
abbrev localEvaluationModules (X : Scheme.{u}) (U : X.Opens) :=
  SheafOfModules.{u} ((sheafCompose ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U))

/-- The structure sheaf in degree zero on the localized site.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationUnit (X : Scheme.{u}) (U : X.Opens) :
    CochainComplex (localEvaluationModules X U) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ (localEvaluationModules X U))

/-- The ordinary Hom dual, with its actual Hom-complex differential.
Source: Stacks Project, Tag 08DM
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationDual (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :=
  homComplex (R := X.sheaf.over U) P (localEvaluationUnit X U)

/-- The total tensor with the ordinary Hom dual.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationTensor (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ) :=
  CochainComplex.mapBifunctor F (localEvaluationDual X U P) (curriedTensor _)

/-- The specified product projection of the recorded Hom complex.
Source: Stacks Project, Tag 08DM
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationProjection (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (n r s : ℤ) (h : r + n = s) :
    (homComplex (R := X.sheaf.over U) P F).X n ⟶
      SheafOfModules.homObj (R := X.sheaf.over U) (P.X r) (F.X s) :=
  (Classical.choose (Classical.choose_spec
    (homComplex_exists (R := X.sheaf.over U)))) P F n r s h

/-- The ordinary evaluation on a tensor summand, followed by a Hom projection.
It is zero unless the dual degree cancels the input degree; otherwise it sends
`y tensor phi` to `x ↦ y * phi(x)`, using the unit action on the second module.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationComponent (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (p q n r : ℤ) (hpq : p + q = n) :
    F.X p ⊗ (localEvaluationDual X U P).X q ⟶
      SheafOfModules.homObj (R := X.sheaf.over U) (P.X r) (F.X (r + n)) :=
  if h : r + q = 0 then
    SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) (P.X r) _ _
      ((β_ (P.X r) (F.X p ⊗ (localEvaluationDual X U P).X q)).hom ≫
        (α_ (F.X p) ((localEvaluationDual X U P).X q) (P.X r)).hom ≫
        F.X p ◁ ((β_ ((localEvaluationDual X U P).X q) (P.X r)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) (P.X r) _
            (𝟙_ (localEvaluationModules X U))).symm
            (localEvaluationProjection X U P (localEvaluationUnit X U) q r 0 h ≫
              SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
                (HomologicalComplex.singleObjXSelf (.up ℤ) 0
                  (𝟙_ (localEvaluationModules X U))).hom)) ≫
        (ρ_ (F.X p)).hom ≫ (F.XIsoOfEq (by omega : p = r + n)).hom)
  else 0

/-- A chain map has the actual ordinary evaluation formula, with the tensor ordered
as `F tensor Hom(P,O[0])`. This predicate specifies maps, not just objects.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def IsLocalOrdinaryEvaluation (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F) : Prop :=
  ∀ (p q n r : ℤ) (h : p + q = n),
    HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
        (curriedTensor _) (.up ℤ) p q n h ≫ f.f n ≫
      localEvaluationProjection X U P F n r (r + n) rfl =
        localEvaluationComponent X U P F p q n r h

```

## New

The block below, with the definitionally equal projection optimization described above, is in `Sheaf.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly`; the original module has
`public import Sheaf.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly`.

```lean
local instance localEvaluationPreadditive {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    MonoidalPreadditive (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  Classical.choice (SheafOfModules.tensorClosed R).1

/-- The existing module category on the localized site, written in the carrier form
used by internal Hom. This is an abbreviation, not a different module category.
Source: Stacks Project, Tag 08DL
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
abbrev localEvaluationModules (X : Scheme.{u}) (U : X.Opens) :=
  SheafOfModules.{u} ((sheafCompose ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U))

/-- The structure sheaf in degree zero on the localized site.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationUnit (X : Scheme.{u}) (U : X.Opens) :
    CochainComplex (localEvaluationModules X U) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ (localEvaluationModules X U))

/-- The ordinary Hom dual, with its actual Hom-complex differential.
Source: Stacks Project, Tag 08DM
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationDual (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :=
  homComplex (R := X.sheaf.over U) P (localEvaluationUnit X U)

/-- The total tensor with the ordinary Hom dual.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationTensor (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ) :=
  CochainComplex.mapBifunctor F (localEvaluationDual X U P) (curriedTensor _)

/-- The specified product projection of the recorded Hom complex.
Source: Stacks Project, Tag 08DM
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationProjection (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (n r s : ℤ) (h : r + n = s) :
    (homComplex (R := X.sheaf.over U) P F).X n ⟶
      SheafOfModules.homObj (R := X.sheaf.over U) (P.X r) (F.X s) :=
  (Classical.choose (homComplex_projections_exists (R := X.sheaf.over U))) P F n r s h

/-- The ordinary evaluation on a tensor summand, followed by a Hom projection.
It is zero unless the dual degree cancels the input degree; otherwise it sends
`y tensor phi` to `x ↦ y * phi(x)`, using the unit action on the second module.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationComponent (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (p q n r : ℤ) (hpq : p + q = n) :
    F.X p ⊗ (localEvaluationDual X U P).X q ⟶
      SheafOfModules.homObj (R := X.sheaf.over U) (P.X r) (F.X (r + n)) :=
  if h : r + q = 0 then
    SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) (P.X r) _ _
      ((β_ (P.X r) (F.X p ⊗ (localEvaluationDual X U P).X q)).hom ≫
        (α_ (F.X p) ((localEvaluationDual X U P).X q) (P.X r)).hom ≫
        F.X p ◁ ((β_ ((localEvaluationDual X U P).X q) (P.X r)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) (P.X r) _
            (𝟙_ (localEvaluationModules X U))).symm
            (localEvaluationProjection X U P (localEvaluationUnit X U) q r 0 h ≫
              SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
                (HomologicalComplex.singleObjXSelf (.up ℤ) 0
                  (𝟙_ (localEvaluationModules X U))).hom)) ≫
        (ρ_ (F.X p)).hom ≫ (F.XIsoOfEq (by omega : p = r + n)).hom)
  else 0

/-- A chain map has the actual ordinary evaluation formula, with the tensor ordered
as `F tensor Hom(P,O[0])`. This predicate specifies maps, not just objects.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def IsLocalOrdinaryEvaluation (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F) : Prop :=
  ∀ (p q n r : ℤ) (h : p + q = n),
    HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
        (curriedTensor _) (.up ℤ) p q n h ≫ f.f n ≫
      localEvaluationProjection X U P F n r (r + n) rfl =
        localEvaluationComponent X U P F p q n r h

```

## Users

The table conservatively includes every transitive importer reported by
`tools/downstream.py`, plus the item itself. The `--uses localEvaluationProjection`
textual hits are the item and `OrdinaryEvaluationDifferential`. The latter
and the other two direct users compile unchanged against the new definition.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | K4 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusShift | C3 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffinePullbackPerfectDetectsIso | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Y3 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.CompactObjectPerfectWitness | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DQCoheratorDerivedGlobalSections | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactDetection | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactRepresentatives | B3 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDerivedMate | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | X2 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferential | A3 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PerfectHomGap | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PerfectObjectCompact | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PerfectRHomEvaluationIsomorphisms | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PerfectSupportedStabilizedLift | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PerfectTensorHomDuality | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | V1 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperPerfectCompactTests | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperPerfectPreservesCompact | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperPerfectTransportCompact | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonProjection | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCase | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons | W4 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationModel | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation | C2 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectRHomEvaluationLocal | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLiftCore | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SupportedMapAffineAttachment | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SupportedMapAffineUnionGluing | P3 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| TargetsCheck | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Definitionally equal constants, same signatures and public visibility; no downstream edit. |

No target declaration changes. The projection body change reopens the meaning check
for any target using it; definitional equality with the old body establishes that its
meaning is unchanged. Transitive downstream modules receive the same public imports through
BoundedOrdinaryEvaluationAssembly. No signature change or forced adaptation is needed; the second reader can
compile the direct users against the sandbox to verify the preserved reexports.

## Status

landed 20261013T045517-L-125548 2026-10-13 (merge of deliver/C2/Sheaf.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation)
