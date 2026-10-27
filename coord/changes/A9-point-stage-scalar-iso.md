# WeilConjectures.pointStageFibreScalarIso

## Reason

Explicit associator arguments avoid inferring the same large coefficient functors
repeatedly. The canonical composition is identical after elaboration; its public
signature, comparison data, and exported reduction status are unchanged. Local
irreducibility protects the composition within this module only. The new scalar
proof initially exceeded the compile limit, so this is an elaboration optimization.
No target statement or mathematical definition is altered.

## Old

```lean
noncomputable def pointStageFibreScalarIso
    (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) :
    GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω (Spec (.of D.k)) F G h ⋙
        pointStageFibre D l hl Ω G ≅
      pointStageFibre D l hl Ω F ⋙
        DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom :=
  (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      (CategoryTheory.Functor.isoWhiskerRight
          (eqToIso ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
            l Ω (Spec (.of D.k))).exists.choose_spec.1 F G h))
          (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)) ≪≫
        pointRationalFibreScalarIso D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h))
      (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom) ≪≫
    CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft _ (pointStageTensorSquare l Ω F G h) ≪≫
    (CategoryTheory.Functor.associator _ _ _).symm

```

## New

```lean
noncomputable def pointStageFibreScalarIso
    (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) :
    GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω (Spec (.of D.k)) F G h ⋙
        pointStageFibre D l hl Ω G ≅
      pointStageFibre D l hl Ω F ⋙
        DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom :=
  (CategoryTheory.Functor.associator
      (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω (Spec (.of D.k)) F G h)
      (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G))
      (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom)).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      (CategoryTheory.Functor.isoWhiskerRight
          (eqToIso ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
            l Ω (Spec (.of D.k))).exists.choose_spec.1 F G h))
          (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)) ≪≫
        pointRationalFibreScalarIso D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h))
      (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom) ≪≫
    CategoryTheory.Functor.associator
      (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
      (DerivedCategory.pointFdScalarExtension
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h).toRingHom)
      (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft _ (pointStageTensorSquare l Ω F G h) ≪≫
    (CategoryTheory.Functor.associator
      (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
      (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] F.val).toRingHom)
      (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom)).symm

```

## Users

Listed by `tools/downstream.py Sheaf.Paper.FiniteCoefficientPoint --uses pointStageFibreScalarIso`.
Both original consumers compiled against the delivered module with `lcompile.py --all`.
No consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.FiniteCoefficientPoint` | A9 | Own item; scalar proof and coherent comparisons. |
| `Sheaf.Paper.PointFibreEquivalence` | unclaimed | Original source compiled against this module; no adaptation. |
| `Sheaf.Paper.PointRationalFamilyCommonStageNaturality` | unclaimed | Original source compiled against this module; no adaptation. |

## Status

landed 20261026T000931-L-4148363 2026-10-26 (merge of deliver/A9/Sheaf.Paper.FiniteCoefficientPoint)
