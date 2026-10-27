# AlgebraicGeometry.ProEtale.restrictionLocal

## Reason

Complete the existing local exceptional-pullback theorem without changing its signature.
The full-subcategory coefficient equivalences and composite adjunctions need explicit
instance transport and controlled elaboration. All helpers are private and proved, and all
mathematical objects are constructed from existing functors and equivalences.

## Old

The public theorem `AlgebraicGeometry.ProEtale.restrictionLocal` has its current signature
and proof `:= by sorry`. Its public imports and `set_option autoImplicit false` are unchanged.
The original signature is:

```lean
theorem restrictionLocal
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (cf : Compactification.BoundaryCompactification f)
    (hf : ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      localizingClosureProEtale Λ X K →
        localizingClosureProEtale Λ Y
          ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cf.obj.obj).obj K))
    (Ff : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (_adjf : CondensedRing.localizingLowerShriek Λ cf.obj.obj hf ⊣ Ff) :
    (∀ {V U : Scheme.{u}} (v : V ⟶ Y) (u : U ⟶ X)
        (hV : IsAffine V) (hU : IsAffine U)
        (hv : IsOpenImmersion v) (hu : IsOpenImmersion u)
        (d : ℕ)
        (i : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
        (hi : IsClosedImmersion i)
        (q : U ⟶ V)
        (hqi : i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom = q)
        (hq : q ≫ v = u ≫ f)
        (cp : Compactification.BoundaryCompactification
          ((AffineSpace.over (ULift.{u} (Fin d)) V).hom))
        (hp : ∀ K : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology (AffineSpace
              (ULift.{u} (Fin d)) V)) Ab.{u + 1})
              (condensedRingObj Λ (AffineSpace (ULift.{u} (Fin d)) V))),
          localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V) K →
            localizingClosureProEtale Λ V
              ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cp.obj.obj).obj K))
        (Fp : (localizingClosureProEtale Λ V).FullSubcategory ⥤
          (localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)).FullSubcategory)
        (adjp : CondensedRing.localizingLowerShriek Λ cp.obj.obj hp ⊣ Fp)
        (ci : Compactification.BoundaryCompactification i)
        (hi' : ∀ K : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
              (condensedRingObj Λ U)),
          localizingClosureProEtale Λ U K →
            localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)
              ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ ci.obj.obj).obj K))
        (Fi : (localizingClosureProEtale Λ (AffineSpace
            (ULift.{u} (Fin d)) V)).FullSubcategory ⥤
          (localizingClosureProEtale Λ U).FullSubcategory)
        (adji : CondensedRing.localizingLowerShriek Λ ci.obj.obj hi' ⊣ Fi),
        ∃ (huStar : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
            localizingClosureProEtale Λ U
              (((localizingClosureProEtale Λ X).ι ⋙
                (CondensedRing.upperStar Λ u).leftDerivedFunctor).obj K))
          (hvStar : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
            localizingClosureProEtale Λ V
              (((localizingClosureProEtale Λ Y).ι ⋙
                (CondensedRing.upperStar Λ v).leftDerivedFunctor).obj K)),
          Nonempty
            ((Ff ⋙
                (localizingClosureProEtale Λ U).lift
                  ((localizingClosureProEtale Λ X).ι ⋙
                    (CondensedRing.upperStar Λ u).leftDerivedFunctor) huStar) ≅
              ((localizingClosureProEtale Λ V).lift
                  ((localizingClosureProEtale Λ Y).ι ⋙
                    (CondensedRing.upperStar Λ v).leftDerivedFunctor) hvStar ⋙
                Fp ⋙ Fi)) ∧
          (∀ K : DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
                (condensedRingObj Λ Y)),
            constantModelBoundedConstructible Λ Y K →
              ∃ hK : localizingClosureProEtale Λ Y K,
                constantModelBoundedConstructible Λ U
                  (((localizingClosureProEtale Λ U).lift
                      ((localizingClosureProEtale Λ X).ι ⋙
                        (CondensedRing.upperStar Λ u).leftDerivedFunctor) huStar).obj
                    (Ff.obj ⟨K, hK⟩)).obj)) ∧
      ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (u : ∀ a, U a ⟶ X),
        (∀ a, IsAffine (U a) ∧ IsOpenImmersion (u a)) ∧
        (∀ x : X, ∃ a : Fin n, ∃ y : U a, (u a).base y = x) ∧
        (∀ a, ∃ (V : Scheme.{u}) (v : V ⟶ Y),
          IsAffine V ∧ IsOpenImmersion v ∧
          ∃ (d : ℕ) (i : U a ⟶ AffineSpace (ULift.{u} (Fin d)) V)
            (hi : IsClosedImmersion i) (q : U a ⟶ V),
            i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom = q ∧ q ≫ v = u a ≫ f)
```

## New

The theorem has the identical signature below and a complete proof, with private helpers.

```lean
theorem restrictionLocal
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (cf : Compactification.BoundaryCompactification f)
    (hf : ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      localizingClosureProEtale Λ X K →
        localizingClosureProEtale Λ Y
          ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cf.obj.obj).obj K))
    (Ff : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (_adjf : CondensedRing.localizingLowerShriek Λ cf.obj.obj hf ⊣ Ff) :
    (∀ {V U : Scheme.{u}} (v : V ⟶ Y) (u : U ⟶ X)
        (hV : IsAffine V) (hU : IsAffine U)
        (hv : IsOpenImmersion v) (hu : IsOpenImmersion u)
        (d : ℕ)
        (i : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
        (hi : IsClosedImmersion i)
        (q : U ⟶ V)
        (hqi : i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom = q)
        (hq : q ≫ v = u ≫ f)
        (cp : Compactification.BoundaryCompactification
          ((AffineSpace.over (ULift.{u} (Fin d)) V).hom))
        (hp : ∀ K : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology (AffineSpace
              (ULift.{u} (Fin d)) V)) Ab.{u + 1})
              (condensedRingObj Λ (AffineSpace (ULift.{u} (Fin d)) V))),
          localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V) K →
            localizingClosureProEtale Λ V
              ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cp.obj.obj).obj K))
        (Fp : (localizingClosureProEtale Λ V).FullSubcategory ⥤
          (localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)).FullSubcategory)
        (adjp : CondensedRing.localizingLowerShriek Λ cp.obj.obj hp ⊣ Fp)
        (ci : Compactification.BoundaryCompactification i)
        (hi' : ∀ K : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
              (condensedRingObj Λ U)),
          localizingClosureProEtale Λ U K →
            localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)
              ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ ci.obj.obj).obj K))
        (Fi : (localizingClosureProEtale Λ (AffineSpace
            (ULift.{u} (Fin d)) V)).FullSubcategory ⥤
          (localizingClosureProEtale Λ U).FullSubcategory)
        (adji : CondensedRing.localizingLowerShriek Λ ci.obj.obj hi' ⊣ Fi),
        ∃ (huStar : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
            localizingClosureProEtale Λ U
              (((localizingClosureProEtale Λ X).ι ⋙
                (CondensedRing.upperStar Λ u).leftDerivedFunctor).obj K))
          (hvStar : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
            localizingClosureProEtale Λ V
              (((localizingClosureProEtale Λ Y).ι ⋙
                (CondensedRing.upperStar Λ v).leftDerivedFunctor).obj K)),
          Nonempty
            ((Ff ⋙
                (localizingClosureProEtale Λ U).lift
                  ((localizingClosureProEtale Λ X).ι ⋙
                    (CondensedRing.upperStar Λ u).leftDerivedFunctor) huStar) ≅
              ((localizingClosureProEtale Λ V).lift
                  ((localizingClosureProEtale Λ Y).ι ⋙
                    (CondensedRing.upperStar Λ v).leftDerivedFunctor) hvStar ⋙
                Fp ⋙ Fi)) ∧
          (∀ K : DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
                (condensedRingObj Λ Y)),
            constantModelBoundedConstructible Λ Y K →
              ∃ hK : localizingClosureProEtale Λ Y K,
                constantModelBoundedConstructible Λ U
                  (((localizingClosureProEtale Λ U).lift
                      ((localizingClosureProEtale Λ X).ι ⋙
                        (CondensedRing.upperStar Λ u).leftDerivedFunctor) huStar).obj
                    (Ff.obj ⟨K, hK⟩)).obj)) ∧
      ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (u : ∀ a, U a ⟶ X),
        (∀ a, IsAffine (U a) ∧ IsOpenImmersion (u a)) ∧
        (∀ x : X, ∃ a : Fin n, ∃ y : U a, (u a).base y = x) ∧
        (∀ a, ∃ (V : Scheme.{u}) (v : V ⟶ Y),
          IsAffine V ∧ IsOpenImmersion v ∧
          ∃ (d : ℕ) (i : U a ⟶ AffineSpace (ULift.{u} (Fin d)) V)
            (hi : IsClosedImmersion i) (q : U a ⟶ V),
            i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom = q ∧ q ≫ v = u a ≫ f)
```
The following lexical proof context is added:

```lean
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalClosed DerivedCategory.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.mateOpenTrivialLowerShriek
  AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso
```

The private helper section additionally sets
`backward.isDefEq.respectTransparency.types true`; this is restored to `false` before
the original public signature and enabled again only inside its proof. This reduces
repeated type elaboration without changing its terms or the public interface; the full
proof compiled in 41.9 seconds, improving the earlier 56.9-second compile and avoiding
the first delivery preflight timeout.

The coefficient transport helpers use `backward.isDefEq.respectTransparency true`
locally. Private `coefficientGenerators` and `coefficientDerived` definitions spell out
the existing generating predicate and derived scalar restriction once; neither changes
its data. Its equivalence proof is `shriekCoefficientIso_transport`, and inverse transport
uses the existing private `transportCompIso`; no duplicate scalar-change constructions
remain. The shift comparison is the existing map-derived-category comparison. The private `conjugate_preservation` and `chart_comparison` theorems do the
formal adjunction calculations over abstract categories before specializing to the
actual derived module categories.

Private declarations use local heartbeat budgets of 80000; the main theorem uses
400000. The theorem locally disables `linter.unusedVariables` because the fixed public
statement names proof binders used only implicitly in its conclusion; none is renamed.
These settings do not change definitions, exported instances or target meanings.
The main proof body uses stricter term transparency, while its unchanged signature
retains the original instance elaboration settings. `open CondensedRing`
is lexical. The three `import all` proof imports expose existing private pullback and
coefficient-transport lemmas to this proof only; no private declaration occurs in the
public theorem type or a public definition.

## Users

`tools/downstream.py Sheaf.Paper.RestrictionLocal --uses restrictionLocal` reports the
transitive consumers below and finds only one external source use, in
`Sheaf.SixFunctors.IntegralRestrictionChartCover`. The theorem's type and every public import
are byte-for-byte unchanged. The added options, open command and local irreducibility
attributes end at this module. No consumer requires adaptation and no target statement changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.RestrictionLocal | C3 | Existing theorem proved; private proof context only. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | B2 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged public interface; no adaptation. |
| TargetsCheck | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.Statement | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Main | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Product | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Unchanged public interface; no adaptation. |

## Status

landed 20261025T015416-L-337419 2026-10-25 (merge of deliver/C3/Sheaf.Paper.RestrictionLocal)
