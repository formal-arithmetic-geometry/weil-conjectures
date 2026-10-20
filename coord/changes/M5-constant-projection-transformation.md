# constantDerivedProjectionMap

## Reason

The bounded-below proof needs naturality of the actual counit mate. Name that
transformation with its type inferred from its defining expression, and prove its
component equation. Keep the existing component definition's signature and body
verbatim, including the concurrent J5 cached-comparison interface and its equation.
This lets existing consumers continue to unfold and generalize the defining adjunction.

Add normalized source and target functors with reflexive equations identifying them
with the transformation's functors. Name the existing derived constant functor,
cache its existing shift construction, and prove triangulated exactness generically.
Use the inherited abelian additive and zero structures consistently, and cache the
existing sheaf tensor additivity as a proved theorem. Every new definition is an
explicit construction and every new theorem is proved. These auxiliary interfaces
preserve the canonical projection morphism.

## Old

In the existing coefficient-category variable context:

```lean
noncomputable def constantDerivedProjectionMap (X : Scheme.{u})
    [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory A) :
    (((rightDerivedGlobalSections A X) ⋙
      curriedTensor (DerivedCategory A)).obj E).obj K ⟶
    (((Functor.postcompose₂.obj (rightDerivedGlobalSections A X)).obj
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
        (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor).obj
          (curriedTensor _))).obj E).obj K :=
  (((derivedConstantGlobalSectionsAdjunction A X).rightAdjointProjectionMap
    (constantSheaf X.smallEtaleTopology A).cachedDerivedTensorComparison).app
      E).app K
```

## New

Every existing declaration signature and attribute, and every existing public import,
is retained verbatim. Add the public import
`WeilConjectures.SixFunctors.Etale.Derived.GlobalSections` because the new shift data use
its named shift construction. The concurrent J5 cached-comparison declarations, attributes and defining equation
are preserved verbatim. The new transformation uses that same cached comparison; its
body is the current component body before its two evaluations. The existing component
definition's body stays verbatim, and a new reflexive equation relates it to the named
transformation. Its component equation, and the normalized source
and target equations, are reflexive. No target statement or its meaning changes.

```lean
-- Use the additive structure supplied by the abelian instance throughout derivation.
attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local instance 21000] sheafBraidedCategory

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

omit [HasSmallSiteSheafify A] [Abelian.HasFunctorialFlatResolution A] in
/-- The existing tensor additivity, expressed using the additive structure inherited
from the abelian sheaf category. Source: Stacks Tag 07A4
(blueprint: def-kun-constant-projection-morphism). -/
theorem constantProjectionSheafMonoidalPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive (Sheaf X.smallEtaleTopology A) := by
  infer_instance

attribute [local instance 50000] constantProjectionSheafMonoidalPreadditive

/-- The unbounded adjunction of derived constant sheaves and derived global sections.
Source: Stacks Tag 07A6 (blueprint: def-kun-constant-projection-morphism).
Exactness identifies the left derived functor with termwise constant sheaves. -/
noncomputable def derivedConstantGlobalSectionsAdjunction (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor ⊣
      rightDerivedGlobalSections A X :=
  (constantSheafΓAdj X.smallEtaleTopology A).derivedAdjunction

/-- The natural transformation whose components are the canonical constant projection
maps. Source: Stacks Tags 07A4, 07A6 and 0B56
(blueprint: def-kun-constant-projection-morphism). The type is inferred from the
canonical mate to retain its actual derived tensor structures. -/
noncomputable def constantDerivedProjectionTransformation (X : Scheme.{u})
    [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat] :=
  (derivedConstantGlobalSectionsAdjunction A X).rightAdjointProjectionMap
    (constantSheaf X.smallEtaleTopology A).cachedDerivedTensorComparison

/-- The derived constant functor with its instance data fixed once.
Source: Stacks Tag 07A6 (blueprint: def-kun-constant-projection-morphism). -/
noncomputable def constantProjectionLeftDerived (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor

/-- The source functor of the canonical constant projection transformation.
Source: Stacks Tag 0B56 (blueprint: def-kun-constant-projection-morphism). -/
noncomputable def constantProjectionSource (X : Scheme.{u})
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  (curriedTensor (DerivedCategory A)).obj ((rightDerivedGlobalSections A X).obj E)

/-- The target functor of the canonical constant projection transformation.
Source: Stacks Tag 0B56 (blueprint: def-kun-constant-projection-morphism). -/
noncomputable def constantProjectionTarget (X : Scheme.{u})
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  constantProjectionLeftDerived A X ⋙
    (curriedTensor _).obj E ⋙ rightDerivedGlobalSections A X

omit [HasSmallSiteSheafify A] in
/-- Source formula for the native projection transformation.
Source: Stacks Tag 0B56 (blueprint: def-kun-constant-projection-morphism). -/
theorem constantProjectionSource_eq (X : Scheme.{u})
    [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    constantProjectionSource A X E =
      (Arrow.mk ((constantDerivedProjectionTransformation A X).app E)).left := rfl

omit [HasSmallSiteSheafify A] in
/-- Target formula for the native projection transformation.
Source: Stacks Tag 0B56 (blueprint: def-kun-constant-projection-morphism). -/
theorem constantProjectionTarget_eq (X : Scheme.{u})
    [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    constantProjectionTarget A X E =
      (Arrow.mk ((constantDerivedProjectionTransformation A X).app E)).right := rfl

/-- Shift structure of the exact derived constant-sheaf functor.
Source: Stacks Tag 07A6 (blueprint: def-kun-constant-projection-morphism). -/
@[instance_reducible]
noncomputable def constantLeftDerivedShift (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor.CommShift ℤ :=
  Functor.CommShift.ofIso
    (constantSheaf X.smallEtaleTopology A).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ

omit [HasSmallSiteSheafify A] in
/-- Exactness of the derived constant-sheaf functor with its specified shift structure.
Source: Stacks Tag 07A6 (blueprint: def-kun-constant-projection-morphism). -/
theorem constantLeftDerived_exact (X : Scheme.{u}) :
    let := constantLeftDerivedShift A X
    (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor.IsTriangulated := by
  let C := constantSheaf X.smallEtaleTopology A
  let := constantLeftDerivedShift A X
  have : NatTrans.CommShift C.leftDerivedFunctorIsoMapDerivedCategory.symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility C.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  exact Functor.isTriangulated_of_iso C.leftDerivedFunctorIsoMapDerivedCategory.symm

/-- Shift structure of the source of the projection transformation.
Source: Stacks Tag 0B56 (blueprint: def-kun-constant-projection-morphism). -/
@[instance_reducible]
noncomputable def constantProjectionSourceShift (X : Scheme.{u})
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (constantProjectionSource A X E).CommShift ℤ := by
  dsimp only [constantProjectionSource, Arrow.mk_left, Functor.comp_obj]
  infer_instance

/-- Shift structure of the target of the projection transformation.
Source: Stacks Tag 0B56 (blueprint: def-kun-constant-projection-morphism). -/
@[instance_reducible]
noncomputable def constantProjectionTargetShift (X : Scheme.{u})
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (constantProjectionTarget A X E).CommShift ℤ := by
  let : (constantProjectionLeftDerived A X).CommShift ℤ :=
    constantLeftDerivedShift A X
  let : (rightDerivedGlobalSections A X).CommShift ℤ :=
    commShiftRightDerivedGlobalSections A X
  dsimp only [constantProjectionTarget, Arrow.mk_right, Functor.postcompose₂,
    Functor.whiskeringLeft₂,
    Functor.comp_obj, Functor.whiskeringRight, Functor.whiskeringLeft]
  infer_instance

omit [HasSmallSiteSheafify A] in
/-- The source of the projection transformation is triangulated.
Source: Stacks Tag 0B56 (blueprint: def-kun-constant-projection-morphism). -/
theorem constantProjectionSource_exact (X : Scheme.{u})
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    let := constantProjectionSourceShift A X E
    (constantProjectionSource A X E).IsTriangulated := by
  let := constantProjectionSourceShift A X E
  dsimp only [constantProjectionSource, Arrow.mk_left, Functor.comp_obj]
  infer_instance

omit [HasSmallSiteSheafify A] in
/-- The target of the projection transformation is triangulated.
Source: Stacks Tag 0B56 (blueprint: def-kun-constant-projection-morphism). -/
theorem constantProjectionTarget_exact (X : Scheme.{u})
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    let := constantProjectionTargetShift A X E
    (constantProjectionTarget A X E).IsTriangulated := by
  let : (constantProjectionLeftDerived A X).CommShift ℤ :=
    constantLeftDerivedShift A X
  have : (constantProjectionLeftDerived A X).IsTriangulated := constantLeftDerived_exact A X
  let : (rightDerivedGlobalSections A X).CommShift ℤ :=
    commShiftRightDerivedGlobalSections A X
  have : (rightDerivedGlobalSections A X).IsTriangulated :=
    inferInstanceAs (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor.IsTriangulated
  let := constantProjectionTargetShift A X E
  dsimp only [constantProjectionTarget, Arrow.mk_right, Functor.postcompose₂,
    Functor.whiskeringLeft₂,
    Functor.comp_obj, Functor.whiskeringRight, Functor.whiskeringLeft]
  infer_instance

/-- The canonical map `RΓ(E) ⊗ᴸ K → RΓ(E ⊗ᴸ K̲)`, defined as the adjunct of the
canonical derived constant-sheaf tensor comparison followed by the counit on `E`.
Source: Stacks Tag 0F12 and equation 0B56
(blueprint: def-kun-constant-projection-morphism). The tensor comparison is the existing
left-derived comparison, characterized by its ordinary comparison on K-flat models. -/
noncomputable def constantDerivedProjectionMap (X : Scheme.{u})
    [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory A) :
    (((rightDerivedGlobalSections A X) ⋙
      curriedTensor (DerivedCategory A)).obj E).obj K ⟶
    (((Functor.postcompose₂.obj (rightDerivedGlobalSections A X)).obj
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
        (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor).obj
          (curriedTensor _))).obj E).obj K :=
  (((derivedConstantGlobalSectionsAdjunction A X).rightAdjointProjectionMap
    (constantSheaf X.smallEtaleTopology A).cachedDerivedTensorComparison).app
      E).app K

omit [HasSmallSiteSheafify A] in
/-- Component equation for the canonical projection natural transformation.
Source: Stacks equation 0B56 (blueprint: def-kun-constant-projection-morphism). -/
theorem constantDerivedProjectionMap_eq_transformation (X : Scheme.{u})
    [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) (K : DerivedCategory A) :
    constantDerivedProjectionMap A X E K =
      ((constantDerivedProjectionTransformation A X).app E).app K := rfl

```

## Users

The table includes all transitive importers reported by downstream.py and the module
itself. Direct textual users of the changed definition are this module, the assigned
bounded-below theorem, EtaleConstantProjectionFormula, and FiniteMappingAdjunction.
No consumer signature or definition needs adaptation: the existing map signature is
verbatim and its value is definitionally identical. The historical validation copies of
EtaleConstantProjectionFormula and FiniteMappingAdjunction compiled unchanged. During
validation J5 updated the former, and the latter moved to the quarantine path recorded
in rework.tsv. The current J5 consumer compiled unchanged in 26.2 seconds after preserving its
cached-comparison API and the existing component body. The final map, bounded-flat
statement, approximation and main theorem compiled in 7.2, 2.7, 9.7 and 3.8 seconds,
respectively. The axiom check for the approximation and exactness API contains only
propext, Classical.choice and Quot.sound; the main theorem contains sorryAx from the
explicit bounded-flat source case. The quarantine archive is untouched; its temporary validation
copy is excluded from this delivery. The table records the users found at the initial
read, with this quarantine update noted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula | J5 | Definitionally identical map; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow | M5 | Assigned proof uses the named transformation and naturality. |
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap | unclaimed | Package the same mate; add reflexive component and functor formulas. |
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionFlatApproximation | new, M5 | Uses the named derived constant functor, source, target, shifts and exactness APIs; compiles. |
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionBoundedFlat | new, M5 | Uses the retained canonical map in its statement; compiles. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | M7 | Definitionally identical map; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.GeometricPointPullbackTensorNormalization | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing | G7 | Definitionally identical map; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | P7 | Definitionally identical map; existing signatures unchanged. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.DirectImageCtfOpenTor | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.ExternalRHomConePairing | J7 | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | quarantined | Archive unchanged; historical copy compiled without adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Definitionally identical map; existing signatures unchanged. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Definitionally identical map; existing signatures unchanged. |

## Status

landed 20261020T221249-L-4165663 2026-10-20 (merge of deliver/M5/Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow)
