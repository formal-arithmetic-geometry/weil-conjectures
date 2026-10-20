# PurityFrameClass degree-zero derived constructions

## Reason

The four theorem holes have complete proofs. Profiling showed kernel checking spent
about 10 seconds on `frameTensorNext` and substantial time converting bounded-below single
functor objects in `frameCupSheaves`. These conversions unfold a large localization.
The tensor/cup revision compiled cleanly in 38.6 seconds. The final variant passed the
delivery compilation and axiom probe within the unchanged 60-second limit.
The file-local `Elab.async false` schedules elaboration sequentially; it is not exported
and changes no definition or mathematical statement.

`frameSingleTensorMap` is a generic wrapper for the existing `cupDerivedCoefficientMap`.
Its single functor parameter is identified by equality with the ordinary single functor.
Substitution proves the wrapper is exactly the existing map. Its specialization avoids
unfolding the named single functor repeatedly in the kernel. This is a genuine construction,
with no choice from an unproved existence statement.

`frameCupSheaves` still calls `supportedCup` itself. Its bounded-below inputs are now
constructed directly from the same underlying single objects, with their degree-zero
lower bounds proved by the existing single-functor instance. Thus the underlying objects
agree syntactically with the declared result, avoiding a functor-wrapper conversion.

`frameFold` is the ordinary dependent `Nat.rec`, with its result family and prefix
function as parameters. The specialization in `frameBoundaryProduct` reduces to the
original `Nat.rec` expression. This avoids checking the expanded dependent result type
while elaborating the recursor. The full variant compiled in 48.7 seconds, with only an
unused binder warning, now corrected to `_d`.

`frameSingleUnit` substitutes the equality between the constant coefficient and zero twist
before applying the functor. Its explicit object arguments keep this conversion in the
sheaf category. The resulting inverse restriction and zero-shift comparison are identical
to the original body. A scratch equality check against the published empty product compiles
using `rfl` in 19.2 seconds. The tensor/cup equality check compiles in 44.4 seconds, and
the fold equality check in 31.4 seconds, each by `rfl`. No arbitrary data is chosen.

All existing signatures, visibility, public imports, and mathematical constructions stay
unchanged. The generic tensor, unit and fold wrappers are public because public definitions
use them. Only the item module changes; all downstream statements retain their meaning, including targets.
No target semantic review needs reopening.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def frameTensorNext (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :
    cupTensorObject P X ((cupSingle P X).obj (P.frameTwist X d))
        ((cupSingle P X).obj (P.frameTwist X 1)) ⟶
      (cupSingle P X).obj (P.frameTwist X (d + 1)) :=
  cupSingleTensorMap (hD := cupHasDerivedCategory P X) (hDM := cupMonoidal P X)
    (P.frameTwist X d) (P.frameTwist X 1) ≫
      (cupSingle P X).map (P.frameSheafTensorNext X d).hom

def frameEmptyClass (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (f : Fin 0 → Γ(X, ⊤)) :
    cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
      ((cupSingle P X).obj (P.frameTwist X 0)) 0 :=
  (cupSingle P X).map
    (@inv _ _ _ _ (cupCoefficientRestriction P (X.zeroLocusSubschemeι (Set.range f)))
      (P.frameEmptyRestriction_isIso X f)) ≫
    (shiftFunctorZero (CupDerivedCategory P X) ℤ).inv.app _

def frameCupSheaves (P : PurityFiniteSetting.{u}) {Z W X : Scheme.{u}}
    (s : X ⟶ Spec (.of P.field.k)) (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    (a b : ℤ) (α : cupSupportedHom P i ((cupSingle P X).obj F) a)
    (β : cupSupportedHom P j ((cupSingle P X).obj G) b) :
    cupSupportedHom P (cupIntersection i j)
      (cupTensorObject P X ((cupSingle P X).obj F) ((cupSingle P X).obj G)) (a + b) :=
  letI : X.Over (Spec (.of P.field.k)) := ⟨s⟩
  supportedCup P i j
    ((@DerivedCategory.Plus.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
      _ _ (cupHasDerivedCategory P X) 0).obj F)
    ((@DerivedCategory.Plus.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
      _ _ (cupHasDerivedCategory P X) 0).obj G) a b α β

def frameBoundaryProduct (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) :
    (c : ℕ) → (f : Fin c → Γ(X, ⊤)) →
      cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
        ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ))
  := Nat.rec (fun f ↦ P.frameEmptyClass X f)
    (fun d previous f ↦ P.frameCupNext X a d f
      (previous (fun k : Fin d ↦ f k.castSucc)))

```

## New

```lean
set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def frameSingleTensorMap {C : Type v} [Category.{w} C] [Abelian C]
    [hD : HasDerivedCategory.{w} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    (S : C ⥤ DerivedCategory C) (hS : S = DerivedCategory.singleFunctor C 0)
    {L M N : C} (μ : L ⊗ M ⟶ N) :
    ((curriedTensor (DerivedCategory C)).obj (S.obj L)).obj (S.obj M) ⟶ S.obj N := by
  subst S
  exact cupDerivedCoefficientMap μ

def frameTensorNext (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :
    cupTensorObject P X ((cupSingle P X).obj (P.frameTwist X d))
        ((cupSingle P X).obj (P.frameTwist X 1)) ⟶
      (cupSingle P X).obj (P.frameTwist X (d + 1)) :=
  frameSingleTensorMap (hD := cupHasDerivedCategory P X) (hDM := cupMonoidal P X)
    (cupSingle P X) rfl (P.frameSheafTensorNext X d).hom

def frameSingleUnit {C : Type v} [Category.{w} C] {D : Type*} [Category D]
    [HasShift D ℤ] (S : C ⥤ D) {L M N : C} (q : L ⟶ M) (hq : IsIso q) (h : L = N) :
    S.obj M ⟶ (S.obj N)⟦(0 : ℤ)⟧ := by
  subst N
  exact S.map (@inv _ _ _ _ q hq) ≫ (shiftFunctorZero D ℤ).inv.app _

def frameEmptyClass (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (f : Fin 0 → Γ(X, ⊤)) :
    cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
      ((cupSingle P X).obj (P.frameTwist X 0)) 0 :=
  frameSingleUnit (cupSingle P X)
    (L := P.constant X) (N := P.frameTwist X 0)
    (M := (lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (X.zeroLocusSubschemeι (Set.range f))).obj
        (P.constant (X.zeroLocusSubscheme (Set.range f))))
    (cupCoefficientRestriction P (X.zeroLocusSubschemeι (Set.range f)))
    (P.frameEmptyRestriction_isIso X f) rfl

def frameCupSheaves (P : PurityFiniteSetting.{u}) {Z W X : Scheme.{u}}
    (s : X ⟶ Spec (.of P.field.k)) (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    (a b : ℤ) (α : cupSupportedHom P i ((cupSingle P X).obj F) a)
    (β : cupSupportedHom P j ((cupSingle P X).obj G) b) :
    cupSupportedHom P (cupIntersection i j)
      (cupTensorObject P X ((cupSingle P X).obj F) ((cupSingle P X).obj G)) (a + b) :=
  letI : X.Over (Spec (.of P.field.k)) := ⟨s⟩
  supportedCup P i j
    ⟨(cupSingle P X).obj F, ⟨0, by
      change DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.singleFunctor _ 0).obj _) 0
      infer_instance⟩⟩
    ⟨(cupSingle P X).obj G, ⟨0, by
      change DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.singleFunctor _ 0).obj _) 0
      infer_instance⟩⟩ a b α β

def frameFold {A : ℕ → Type v} {H : (c : ℕ) → A c → Type w}
    (base : (f : A 0) → H 0 f) (takePrefix : (d : ℕ) → A (d + 1) → A d)
    (step : (d : ℕ) → (f : A (d + 1)) → H d (takePrefix d f) → H (d + 1) f) :
    (c : ℕ) → (f : A c) → H c f :=
  Nat.rec base (fun d previous f ↦ step d f (previous (takePrefix d f)))

def frameBoundaryProduct (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) :
    (c : ℕ) → (f : Fin c → Γ(X, ⊤)) →
      cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
        ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ))
  := frameFold (fun f ↦ P.frameEmptyClass X f)
    (fun _d f k ↦ f k.castSucc) (fun d f α ↦ P.frameCupNext X a d f α)

```

## Users

`python3 tools/downstream.py Sheaf.Paper.PurityFrameClass` reports the following
148 downstream modules. All existing signatures, definitions and public imports
are preserved, and the new import is proof-only. No consumer requires adaptation.
Holders are the claims snapshot at preparation; no consumer is edited.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.PurityFrameClass` | K6 | Four holes proved; equivalent tensor and cup bodies avoid reduction. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.CartierClassAgreement` | U5 | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | H7 | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.FiniteHorizontalShriekMate` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.LocalizedTopChern` | E5 | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.PurityDivisorClass` | J7 | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.PurityExteriorProductFrame` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.PurityFrameIndependence` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | K7 | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | W5 | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.RegularImmersionCancellation` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.RegularImmersionClassData` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.RegularImmersionExteriorClass` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.RegularImmersionPurity` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.RegularImmersionSignedEvaluation` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Same signatures and definitions; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Same signatures and definitions; no adaptation. |
| `TargetsCheck` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveTopCohomology` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierStalk` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.LissePoincarePairing` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.OpenClosedTriangle` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDual` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Same signatures and definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Same signatures and definitions; no adaptation. |

## Status

landed 20261020T051458-L-1693305 2026-10-20 (merge of deliver/K6/Sheaf.Paper.PurityFrameClass)
