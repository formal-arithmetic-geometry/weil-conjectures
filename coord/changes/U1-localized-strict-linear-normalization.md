# SheafOfModules.LocalizedStrictTensor.LinearEvaluation

## Reason

Use NormalizedExactDescent for the coefficient-linear normalization field, with
explicit additive and exactness instances. This is precisely the former expanded
equation, including its scalarComparisonOnComplexes chain map, after unfolding
the shared predicate. The shared expression avoids repeated expansion of exact
localized extension and scalar cochain models in generic comparison applications.
The evaluated field similarly uses DerivedEvaluationSquare, with exactly the former
component equation after unfolding evaluationExtensionDerived and
scalarExtensionDerived. No field, hypothesis, conclusion, or universe changes
mathematically. Definitions
used by targets therefore require the normal independent meaning check again.

## Old

```lean
structure LinearEvaluation
    (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V))
    (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ)
    (η : localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
      reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        towerExtension.{c, v, r} R V)
    (ρ : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ m.F.obj S ≅
      mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        (towerExtension.{c, v, r} R V).mapDerivedCategory) where
  /-- Canonically normalized evaluation on the base site. -/
  base : EvaluationModel.{c, v, r} R m S n
  /-- Canonically normalized evaluation on the slice site. -/
  slice : EvaluationModel.{max c v, v, r} (R.over V) mV
    (S ⋙ sliceAlgebras.{c, v, r} R V) n
  /-- Underlying extension is extension after scalar restriction. -/
  restriction :
    scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)) ⋙
        localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} (S.obj n).right V ⋙
        scalars.{c, v, r} R (S.obj n)
  /-- The comparison preserves extension generators. -/
  restriction_normalized : ScalarExtensionNormalized.{c, v, r} R V (S.obj n) restriction
  /-- The genuinely S_n-linear ordinary projection comparison. -/
  ordinary : localizedSystemExtension.{c, v, r} R V ⋙ base.scalar.E ≅
    slice.scalar.E ⋙ localizedSystemExtension.{c, v, r} (S.obj n).right V
  /-- After restricting coefficients it is exactly the specified tower component. -/
  ordinary_square : ∀ M : Modules.{max c v, v, r} (R.over V),
    (η.hom.app M).app n ≫
      (localizedSystemExtension.{c, v, r} R V).map (slice.ordinary.hom.app M) ≫
      restriction.hom.app (slice.scalar.E.obj M) =
    base.ordinary.hom.app ((localizedSystemExtension.{c, v, r} R V).obj M) ≫
      (scalars.{c, v, r} R (S.obj n)).map (ordinary.hom.app M)
  /-- The coefficient-linear derived projection comparison. -/
  derived : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ base.scalar.T ≅
    slice.scalar.T ⋙
      (localizedSystemExtension.{c, v, r} (S.obj n).right V).mapDerivedCategory
  /-- Its component on every resolving representative is the localized linear chain map. -/
  normalized : ∀ (P : CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ),
    Resolving.{max c v, v, r} (R.over V) P →
    base.scalar.T.map
      ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategoryFactors.hom.app P) ≫
    base.scalar.ε.app
      (((localizedSystemExtension.{c, v, r} R V).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map ((scalarComparisonOnComplexes.{c, v, r} R V (S.obj n)
      base.scalar slice.scalar ordinary).hom.app P) =
    derived.hom.app (DerivedCategory.Q.obj P) ≫
    (localizedSystemExtension.{c, v, r} (S.obj n).right V).mapDerivedCategory.map
      (slice.scalar.ε.app P) ≫
    (localizedSystemExtension.{c, v, r} (S.obj n).right V).mapDerivedCategoryFactors.hom.app
      ((slice.scalar.E.mapHomologicalComplex (.up ℤ)).obj P)
  /-- The evaluated rho is scalar restriction of the linear derived comparison. -/
  evaluated : ∀ K : D.{max c v, v, r} (R.over V),
    (evaluation.{c, v, r} R n).mapDerivedCategory.map (ρ.hom.app K) ≫
      (evaluationExtensionDerived.{c, v, r} R V n).hom.app
        ((mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V)).obj K) ≫
      (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory.map
        (slice.derived.hom.app K) ≫
      (scalarExtensionDerived.{c, v, r} R V (S.obj n) restriction).hom.app
        (slice.scalar.T.obj K) =
    base.derived.hom.app ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategory.obj K) ≫
      (scalars.{c, v, r} R (S.obj n)).mapDerivedCategory.map (derived.hom.app K)
```

## New

```lean
structure LinearEvaluation
    (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V))
    (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ)
    (η : localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
      reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        towerExtension.{c, v, r} R V)
    (ρ : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ m.F.obj S ≅
      mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        (towerExtension.{c, v, r} R V).mapDerivedCategory) where
  /-- Canonically normalized evaluation on the base site. -/
  base : EvaluationModel.{c, v, r} R m S n
  /-- Canonically normalized evaluation on the slice site. -/
  slice : EvaluationModel.{max c v, v, r} (R.over V) mV
    (S ⋙ sliceAlgebras.{c, v, r} R V) n
  /-- Underlying extension is extension after scalar restriction. -/
  restriction :
    scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)) ⋙
        localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} (S.obj n).right V ⋙
        scalars.{c, v, r} R (S.obj n)
  /-- The comparison preserves extension generators. -/
  restriction_normalized : ScalarExtensionNormalized.{c, v, r} R V (S.obj n) restriction
  /-- The genuinely S_n-linear ordinary projection comparison. -/
  ordinary : localizedSystemExtension.{c, v, r} R V ⋙ base.scalar.E ≅
    slice.scalar.E ⋙ localizedSystemExtension.{c, v, r} (S.obj n).right V
  /-- After restricting coefficients it is exactly the specified tower component. -/
  ordinary_square : ∀ M : Modules.{max c v, v, r} (R.over V),
    (η.hom.app M).app n ≫
      (localizedSystemExtension.{c, v, r} R V).map (slice.ordinary.hom.app M) ≫
      restriction.hom.app (slice.scalar.E.obj M) =
    base.ordinary.hom.app ((localizedSystemExtension.{c, v, r} R V).obj M) ≫
      (scalars.{c, v, r} R (S.obj n)).map (ordinary.hom.app M)
  /-- The coefficient-linear derived projection comparison. -/
  derived : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ base.scalar.T ≅
    slice.scalar.T ⋙
      (localizedSystemExtension.{c, v, r} (S.obj n).right V).mapDerivedCategory
  /-- Its component on every resolving representative is the localized linear chain map. -/
  normalized :
    letI := base.scalar.additive
    letI := slice.scalar.additive
    letI := localizedSystemExtensionAdditive.{c, v, r} R V
    letI := localizedSystemExtensionLimits.{c, v, r} R V
    letI := localizedSystemExtensionColimits.{c, v, r} R V
    letI := localizedSystemExtensionAdditive.{c, v, r} (S.obj n).right V
    letI := localizedSystemExtensionLimits.{c, v, r} (S.obj n).right V
    letI := localizedSystemExtensionColimits.{c, v, r} (S.obj n).right V
    NormalizedExactDescent
      (A := Modules.{max c v, v, r} (R.over V)) (B := Modules.{c, v, r} R)
      (C := Modules.{max c v, v, r}
        ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)).right)
      (D := Modules.{c, v, r} (S.obj n).right)
      (localizedSystemExtension.{c, v, r} R V)
      (localizedSystemExtension.{c, v, r} (S.obj n).right V)
      base.scalar.E slice.scalar.E base.scalar.T slice.scalar.T
      base.scalar.ε slice.scalar.ε (Resolving.{max c v, v, r} (R.over V)) ordinary derived
  /-- The evaluated rho is scalar restriction of the linear derived comparison. -/
  evaluated :
    letI := localizedSystemExtensionAdditive.{c, v, r} R V
    letI := localizedSystemExtensionLimits.{c, v, r} R V
    letI := localizedSystemExtensionColimits.{c, v, r} R V
    letI := localizedSystemExtensionAdditive.{c, v, r} (S.obj n).right V
    letI := localizedSystemExtensionLimits.{c, v, r} (S.obj n).right V
    letI := localizedSystemExtensionColimits.{c, v, r} (S.obj n).right V
    DerivedEvaluationSquare
      (A := Modules.{max c v, v, r} (R.over V)) (B := Modules.{c, v, r} R)
      (C := ℕᵒᵖ ⥤ Modules.{max c v, v, r} (R.over V))
      (D := ℕᵒᵖ ⥤ Modules.{c, v, r} R)
      (E := Modules.{max c v, v, r}
        ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)).right)
      (F := Modules.{c, v, r} (S.obj n).right)
      (localizedSystemExtension.{c, v, r} R V) (towerExtension.{c, v, r} R V)
      (evaluation.{c, v, r} R n) (evaluation.{max c v, v, r} (R.over V) n)
      (localizedSystemExtension.{c, v, r} (S.obj n).right V)
      (scalars.{c, v, r} R (S.obj n))
      (scalars.{max c v, v, r} (R.over V)
        ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)))
      (m.F.obj S) (mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V))
      base.scalar.T slice.scalar.T
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) restriction
      ρ base.derived slice.derived derived
```

## Users

`downstream.py --uses LinearEvaluation` lists the defining module and Descent.
CompletedSupportIntermediateTower is the only other transitive importer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.LocalizedStrictTensorLinearEvaluation | unclaimed | Equivalent normalization field; compiled. |
| Sheaf.Algebra.Homology.LocalizedStrictTensorDescent | U1 | Construct the field by normalized exact descent. |
| Sheaf.Paper.CompletedSupportIntermediateTower | unclaimed | No adaptation; consumes Descent with identical fields. |

## Status

landed 20261024T191322-L-305932 2026-10-24 (merge of deliver/U1/Sheaf.Algebra.Homology.LocalizedStrictTensorDescent)
