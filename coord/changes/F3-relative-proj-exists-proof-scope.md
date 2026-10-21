# AlgebraicGeometry.exists_relativeProjData

## Reason

Server preflight classifies the added file-level `open` and elaboration option commands
as an interface change requiring this record. They support the new proof and its private
explicit gluing construction. The theorem signature, public imports, and all pre-existing
public definitions are unchanged. The added helper instances concern the private chart
functor; the independent reader can inspect their scope. The new affine-restriction module
has three proved public lemmas attached to the existing restriction node.

## Old

The original scope command was `open CategoryTheory`. Original theorem signature:

```lean
theorem exists_relativeProjData {X : Scheme.{u}} (A : RelativeProjAlgebra X) :
    ∃ D : RelativeProjData A,
      ∀ (P : Scheme.{u}) (π : P ⟶ X)
        (i : ∀ V : X.affineOpens, (π ⁻¹ᵁ V.1).toScheme ≅ A.localProj V),
        (∀ V : X.affineOpens,
          (i V).hom ≫ A.localBase V ≫ V.1.ι = (π ⁻¹ᵁ V.1).ι ≫ π) →
        (∀ (V W : X.affineOpens) (h : W ≤ V),
          (i W).inv ≫ P.homOfLE (π.preimage_mono h) ≫ (i V).hom =
            A.localTransition h) →
        ∃! e : D.proj ≅ P,
          e.hom ≫ π = D.π ∧
            ∀ V : X.affineOpens,
              (D.restrictionIso V).inv ≫ (D.π ⁻¹ᵁ V.1).ι ≫ e.hom =
                (i V).inv ≫ (π ⁻¹ᵁ V.1).ι 
```

## New

The scope command is `open CategoryTheory Limits Opposite`; the proof also uses
`set_option backward.isDefEq.respectTransparency false` to elaborate the colimit and
cover identifications. These commands apply within this module; no notation or public
attribute is introduced. The theorem has exactly the same signature:

```lean
theorem exists_relativeProjData {X : Scheme.{u}} (A : RelativeProjAlgebra X) :
    ∃ D : RelativeProjData A,
      ∀ (P : Scheme.{u}) (π : P ⟶ X)
        (i : ∀ V : X.affineOpens, (π ⁻¹ᵁ V.1).toScheme ≅ A.localProj V),
        (∀ V : X.affineOpens,
          (i V).hom ≫ A.localBase V ≫ V.1.ι = (π ⁻¹ᵁ V.1).ι ≫ π) →
        (∀ (V W : X.affineOpens) (h : W ≤ V),
          (i W).inv ≫ P.homOfLE (π.preimage_mono h) ≫ (i V).hom =
            A.localTransition h) →
        ∃! e : D.proj ≅ P,
          e.hom ≫ π = D.π ∧
            ∀ V : X.affineOpens,
              (D.restrictionIso V).inv ≫ (D.π ⁻¹ᵁ V.1).ι ≫ e.hom =
                (i V).inv ≫ (π ⁻¹ᵁ V.1).ι 
```

## Users

Audit: `python3 tools/downstream.py Sheaf.AlgebraicGeometry.RelativeProjExists
--uses AlgebraicGeometry.exists_relativeProjData`. Of the downstream modules, only
`Sheaf.AlgebraicGeometry.RelativeProjectiveSpace` mentions the theorem directly. Its
application still has exactly the same type. The table includes the entire transitive
import closure as a conservative audit of the scope-command gate. No consumer's statement
changes meaning, and no consumer needs an adaptation. Holder records were read at the
preflight repair on 2026-10-22.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeProjExists | F3 | Item: proof replaced, signature unchanged. |
| Sheaf.AlgebraicGeometry.CompleteFlagBundle | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.GloballyGeneratedProjectiveBundle | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChangeCoherence | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateGeometry | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateSubschemes | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleFrameModels | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleRankZero | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalData | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeProjectiveSpace | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyVeryAmple | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletion | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletionData | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorProjectiveDehomogenization | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorProjectiveFrameModel | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorProjectivePresentation | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.AmpleNeighbourhood | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.BoundedDimensionProjectiveLocalModel | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.FiniteProjectiveEnvelope | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.ProjectiveBundleProper | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | Unchanged statements and definitions; no adaptation. |

## Status

landed 20261021T214753-L-1850992 2026-10-21 (merge of deliver/F3/Sheaf.AlgebraicGeometry.RelativeProjExists)
