# AlgebraicGeometry.ProEtale.ProjectionSection.backward

## Reason

Profiling found both a quiver-coercion diamond and repeated checking of the
large canonical internal-module structures. Morphism annotations used
`ReflQuiver.toQuiver`, while identities, compositions and functor images used
`CategoryStruct.toQuiver`. The original projection comparison cost 35.6 seconds
of kernel checking; the inverse application cost 49.1 seconds, and the complete
module exceeded 60 seconds. Scoping out `catToReflQuiver` removes that diamond,
following the existing source-library repair in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Limit`.

In addition, all five delivered modules locally select the seven named canonical
structures already defined in `Sheaf.Paper.IntegralResidueDerivedMonoidal`.
These are copies of the existing inferred instances, with no new choices or data.
The module-category, abelian, derived-category, tensor and coefficient-monoid
structures now have compact shared names. The declaration text and construction
body stay verbatim; the inferred structure aliases unfold to the original data.
The two derived-functor aliases remain abbreviations.

`ModuleProjectionSectionArrows` adds a public import of that existing module,
because the public definitions' inferred types use its structure names. The local
registrations below occur in each of the five delivered modules; they do not
register instances for importers. The quiver attribute is scoped to this single
declaration. No source-library declaration or target signature changes. The five
modules compiled together: 28.8, 3.0, 3.1, 3.0 and 41.1 seconds; the last is the
complete normalization proof, with zero holes.

## Old

```lean
def backward {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [IsIso (projection Λ r M ((moduleDerivedPushforward Λ i).obj (𝟙_ _)))]
    [IsIso (sectionArrow Λ r i h M)] : M ⟶ M :=
  (pushforwardSection Λ r i h).inv.app M ≫
    (moduleDerivedPushforward Λ r).map (inv (sectionArrow Λ r i h M)) ≫
    inv (projection Λ r M ((moduleDerivedPushforward Λ i).obj (𝟙_ _))) ≫
    M ◁ (pushforwardSection Λ r i h).hom.app (𝟙_ _) ≫ (ρ_ M).hom
```

## New

```lean
attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

attribute [-instance] CategoryTheory.catToReflQuiver in
def backward {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [IsIso (projection Λ r M ((moduleDerivedPushforward Λ i).obj (𝟙_ _)))]
    [IsIso (sectionArrow Λ r i h M)] : M ⟶ M :=
  (pushforwardSection Λ r i h).inv.app M ≫
    (moduleDerivedPushforward Λ r).map (inv (sectionArrow Λ r i h M)) ≫
    inv (projection Λ r M ((moduleDerivedPushforward Λ i).obj (𝟙_ _))) ≫
    M ◁ (pushforwardSection Λ r i h).hom.app (𝟙_ _) ≫ (ρ_ M).hom
```

## Users

The source-only downstream scan uses the final segment of each name. The table
includes its textual over-approximations and every adapted module; unrelated hits
need no edit. All five adapted modules are compiled together in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.ModuleProjectionSectionArrows | unclaimed | Use the category quiver and named canonical structures; construction text unchanged. |
| Sheaf.Paper.ModuleProjectionSectionComposites | unclaimed | Use the category quiver and named canonical structures; construction text unchanged. |
| Sheaf.Paper.ModuleProjectionSectionInverse | unclaimed | Use the category quiver and named canonical structures; construction text unchanged. |
| Sheaf.Paper.ModuleSectionProjectionArrow | unclaimed | Use the category quiver and named canonical structures; construction text unchanged. |
| Sheaf.Paper.ProjectionSectionNormalization | U6 | Complete the proof; use the category quiver and named canonical structures. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Textual hit is a compiler option or unrelated local name; unchanged. |

## Status

landed 20261021T233805-L-863099 2026-10-21 (merge of deliver/U6/Sheaf.Paper.ProjectionSectionNormalization)
