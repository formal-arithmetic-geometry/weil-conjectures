# Cartesian scheme-test presentation definitions

## Reason

Move the existing presentation definitions to a shared module so effective object descent
and morphism descent can be proved separately without importing the theorem that uses them.
The item publicly reexports that module. No existing declaration changes its signature,
body, namespace, visibility or instance attribute; only blueprint documentation changes.
The added TestLineHom interface expresses morphism descent and has proved identity,
composition and extensionality operations. No target statement or meaning changes.

## Old

In Sheaf.TraceFormula.SpaceLineModuleProjInput:

```lean
/-- Schemes mapping to a presheaf, with commuting triangles as morphisms.
Source: Stacks, Tag 0D2Z (blueprint: def-trf-space-line-module-proj-input). -/
abbrev SchemeTests (F : (Over S)ᵒᵖ ⥤ Type u) := CostructuredArrow yoneda F

/-- The structural map of a scheme test to the scheme base.
Source: Stacks, Tag 0D2Z (blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def testToBase {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (f : F ⟶ yoneda.obj T) (W : SchemeTests F) : W.left ⟶ T :=
  yoneda.preimage (W.hom ≫ f)

/-- A family of invertible modules with specified tensor-pullback identifications.
Coherence and identification with the small-etale module are imposed below.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
structure TestLineFamily (F : (Over S)ᵒᵖ ⥤ Type u) where
  module (W : SchemeTests F) : W.left.left.Modules
  invertible (W : SchemeTests F) : (module W).IsInvertible
  pullbackIso {W V : SchemeTests F} (j : W ⟶ V) :
    (Scheme.Modules.tensorPullback j.left.left).obj (module V) ≅ module W

attribute [instance] TestLineFamily.invertible

/-- Pullback of a global section, using the tensor-formula adjunction normalized by
`1 ⊗ eta(s)`, followed by the specified cartesian identification.
Source: Stacks, Tags 0095, 0096 and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def TestLineFamily.sectionMap {F : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) {W V : SchemeTests F} (j : W ⟶ V)
    (s : Γ(L.module V, ⊤)) : Γ(L.module W, ⊤) :=
  (L.pullbackIso j).hom.app ⊤
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j.left.left)).unit.app
      (L.module V)).val.app (op ⊤) s)

/-- The same pullback on tensor powers, using the existing monoidal comparisons.
Source: Stacks, Tags 01CD and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def TestLineFamily.powerMap {F : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) {W V : SchemeTests F} (j : W ⟶ V) (n : ℕ)
    (s : Γ((L.module V).tensorPow n, ⊤)) : Γ((L.module W).tensorPow n, ⊤) :=
  (Scheme.Modules.boundaryPullbackPowIso j.left.left (L.module V) n ≪≫
    Scheme.Modules.boundaryTensorPowIso (L.pullbackIso j) n).hom.app ⊤
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j.left.left)).unit.app
      ((L.module V).tensorPow n)).val.app (op ⊤) s)

/-- The full identity and composition equations of the cartesian pullback isomorphisms.
These are equations of sheaf isomorphisms, so they include every local section.
Source: Stacks, Tags 03G7 and 0097
(blueprint: def-trf-space-line-module-proj-input). -/
def TestLineFamily.IsCoherent {F : (Over S)ᵒᵖ ⥤ Type u} (L : TestLineFamily F) : Prop :=
  (∀ W : SchemeTests F, L.pullbackIso (𝟙 W) =
    (Scheme.Modules.boundaryPullbackComparison (𝟙 W.left.left)).app (L.module W) ≪≫
      (Scheme.Modules.pullbackId W.left.left).app (L.module W)) ∧
    ∀ (W V Z : SchemeTests F) (j : W ⟶ V) (k : V ⟶ Z),
      L.pullbackIso (j ≫ k) =
        (Scheme.Modules.tensorPullbackCompositionIso j.left.left k.left.left
          (j ≫ k).left.left rfl).app (L.module Z) ≪≫
        (Scheme.Modules.tensorPullback j.left.left).mapIso (L.pullbackIso k) ≪≫
        L.pullbackIso j

/-- Restricting a cartesian family along a map of presheaves is its scheme-test pullback.
There are no choices of objects or morphisms in this construction.
Source: Stacks, Tag 0D2Z(3) (blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def TestLineFamily.pullback {F G : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) (g : G ⟶ F) : TestLineFamily G where
  module W := L.module ((CostructuredArrow.map g).obj W)
  invertible W := L.invertible ((CostructuredArrow.map g).obj W)
  pullbackIso j := L.pullbackIso ((CostructuredArrow.map g).map j)

/-- A cartesian scheme-test presentation of the given small-etale line module.
The additive equivalences are linear over regular functions, and commute with every
small-etale restriction map. Thus the family is the pullback of `line`, not arbitrary
extra line modules on the test schemes.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
structure EtaleLinePresentation (X : AlgebraicSpace S) extends TestLineFamily X.obj.obj where
  coherent : toTestLineFamily.IsCoherent
  line : X.Modules
  isLine : X.IsLineModule line
  etaleSections (T : X.EtaleSite) : Γ(module T.obj, ⊤) ≃+ line.val.obj (op T)
  etaleSections_smul (T : X.EtaleSite) (r : Γ(T.obj.left.left, ⊤))
      (s : Γ(module T.obj, ⊤)) : etaleSections T (r • s) = r • etaleSections T s
  etaleSections_naturality {T U : X.EtaleSite} (j : T ⟶ U)
      (s : Γ(module U.obj, ⊤)) :
    etaleSections T (toTestLineFamily.sectionMap j.hom s) =
      line.val.map j.op (etaleSections U s)

/-- Cartesian isomorphisms of the actual pullback modules on scheme tests.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
structure TestLineIso {F : (Over S)ᵒᵖ ⥤ Type u} (P Q : TestLineFamily F) where
  app (W : SchemeTests F) : P.module W ≅ Q.module W
  naturality {W V : SchemeTests F} (j : W ⟶ V) :
    (P.pullbackIso j).hom ≫ (app W).hom =
      (Scheme.Modules.tensorPullback j.left.left).map (app V).hom ≫ (Q.pullbackIso j).hom

/-- Compatibility with the prescribed small-etale module, rather than only an abstract
isomorphism of the test families. `HEq` uses the fixed equality of the underlying line
modules when applying this predicate to two realizations of the same module.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
def TestLineIso.IsEtaleCompatible {X : AlgebraicSpace S} (P Q : EtaleLinePresentation X)
    (e : TestLineIso P.toTestLineFamily Q.toTestLineFamily) : Prop :=
  ∀ (T : X.EtaleSite) (s : Γ(P.module T.obj, ⊤)),
    HEq (Q.etaleSections T ((e.app T.obj).hom.app ⊤ s)) (P.etaleSections T s)
```

## New

In Sheaf.TraceFormula.SpaceLinePresentationDefs, publicly reexported by the item:

```lean
/-- Schemes mapping to a presheaf, with commuting triangles as morphisms.
Source: Stacks, Tag 0D2Z (blueprint: def-trf-cartesian-line-presentation). -/
abbrev SchemeTests (F : (Over S)ᵒᵖ ⥤ Type u) := CostructuredArrow yoneda F

/-- The structural map of a scheme test to the scheme base.
Source: Stacks, Tag 0D2Z (blueprint: def-trf-cartesian-line-presentation). -/
noncomputable def testToBase {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (f : F ⟶ yoneda.obj T) (W : SchemeTests F) : W.left ⟶ T :=
  yoneda.preimage (W.hom ≫ f)

/-- A family of invertible modules with specified tensor-pullback identifications.
Coherence and identification with the small-etale module are imposed below.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
structure TestLineFamily (F : (Over S)ᵒᵖ ⥤ Type u) where
  module (W : SchemeTests F) : W.left.left.Modules
  invertible (W : SchemeTests F) : (module W).IsInvertible
  pullbackIso {W V : SchemeTests F} (j : W ⟶ V) :
    (Scheme.Modules.tensorPullback j.left.left).obj (module V) ≅ module W

attribute [instance] TestLineFamily.invertible

/-- Pullback of a global section, using the tensor-formula adjunction normalized by
`1 ⊗ eta(s)`, followed by the specified cartesian identification.
Source: Stacks, Tags 0095, 0096 and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
noncomputable def TestLineFamily.sectionMap {F : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) {W V : SchemeTests F} (j : W ⟶ V)
    (s : Γ(L.module V, ⊤)) : Γ(L.module W, ⊤) :=
  (L.pullbackIso j).hom.app ⊤
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j.left.left)).unit.app
      (L.module V)).val.app (op ⊤) s)

/-- The same pullback on tensor powers, using the existing monoidal comparisons.
Source: Stacks, Tags 01CD and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
noncomputable def TestLineFamily.powerMap {F : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) {W V : SchemeTests F} (j : W ⟶ V) (n : ℕ)
    (s : Γ((L.module V).tensorPow n, ⊤)) : Γ((L.module W).tensorPow n, ⊤) :=
  (Scheme.Modules.boundaryPullbackPowIso j.left.left (L.module V) n ≪≫
    Scheme.Modules.boundaryTensorPowIso (L.pullbackIso j) n).hom.app ⊤
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j.left.left)).unit.app
      ((L.module V).tensorPow n)).val.app (op ⊤) s)

/-- The full identity and composition equations of the cartesian pullback isomorphisms.
These are equations of sheaf isomorphisms, so they include every local section.
Source: Stacks, Tags 03G7 and 0097
(blueprint: def-trf-cartesian-line-presentation). -/
def TestLineFamily.IsCoherent {F : (Over S)ᵒᵖ ⥤ Type u} (L : TestLineFamily F) : Prop :=
  (∀ W : SchemeTests F, L.pullbackIso (𝟙 W) =
    (Scheme.Modules.boundaryPullbackComparison (𝟙 W.left.left)).app (L.module W) ≪≫
      (Scheme.Modules.pullbackId W.left.left).app (L.module W)) ∧
    ∀ (W V Z : SchemeTests F) (j : W ⟶ V) (k : V ⟶ Z),
      L.pullbackIso (j ≫ k) =
        (Scheme.Modules.tensorPullbackCompositionIso j.left.left k.left.left
          (j ≫ k).left.left rfl).app (L.module Z) ≪≫
        (Scheme.Modules.tensorPullback j.left.left).mapIso (L.pullbackIso k) ≪≫
        L.pullbackIso j

/-- Restricting a cartesian family along a map of presheaves is its scheme-test pullback.
There are no choices of objects or morphisms in this construction.
Source: Stacks, Tag 0D2Z(3) (blueprint: def-trf-cartesian-line-presentation). -/
noncomputable def TestLineFamily.pullback {F G : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) (g : G ⟶ F) : TestLineFamily G where
  module W := L.module ((CostructuredArrow.map g).obj W)
  invertible W := L.invertible ((CostructuredArrow.map g).obj W)
  pullbackIso j := L.pullbackIso ((CostructuredArrow.map g).map j)

/-- A cartesian scheme-test presentation of the given small-etale line module.
The additive equivalences are linear over regular functions, and commute with every
small-etale restriction map. Thus the family is the pullback of `line`, not arbitrary
extra line modules on the test schemes.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
structure EtaleLinePresentation (X : AlgebraicSpace S) extends TestLineFamily X.obj.obj where
  coherent : toTestLineFamily.IsCoherent
  line : X.Modules
  isLine : X.IsLineModule line
  etaleSections (T : X.EtaleSite) : Γ(module T.obj, ⊤) ≃+ line.val.obj (op T)
  etaleSections_smul (T : X.EtaleSite) (r : Γ(T.obj.left.left, ⊤))
      (s : Γ(module T.obj, ⊤)) : etaleSections T (r • s) = r • etaleSections T s
  etaleSections_naturality {T U : X.EtaleSite} (j : T ⟶ U)
      (s : Γ(module U.obj, ⊤)) :
    etaleSections T (toTestLineFamily.sectionMap j.hom s) =
      line.val.map j.op (etaleSections U s)

/-- Cartesian isomorphisms of the actual pullback modules on scheme tests.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
structure TestLineIso {F : (Over S)ᵒᵖ ⥤ Type u} (P Q : TestLineFamily F) where
  app (W : SchemeTests F) : P.module W ≅ Q.module W
  naturality {W V : SchemeTests F} (j : W ⟶ V) :
    (P.pullbackIso j).hom ≫ (app W).hom =
      (Scheme.Modules.tensorPullback j.left.left).map (app V).hom ≫ (Q.pullbackIso j).hom

/-- Compatibility with the prescribed small-etale module, rather than only an abstract
isomorphism of the test families. `HEq` uses the fixed equality of the underlying line
modules when applying this predicate to two realizations of the same module.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
def TestLineIso.IsEtaleCompatible {X : AlgebraicSpace S} (P Q : EtaleLinePresentation X)
    (e : TestLineIso P.toTestLineFamily Q.toTestLineFamily) : Prop :=
  ∀ (T : X.EtaleSite) (s : Γ(P.module T.obj, ⊤)),
    HEq (Q.etaleSections T ((e.app T.obj).hom.app ⊤ s)) (P.etaleSections T s)
```

The new TestLineHom declarations and their proved operations are in that same module.

## Users

The downstream scan lists 68 transitive modules. The declaration-name scan finds the
following actual text users; the last sectionMap match is a different qualified method.
All existing names remain available by the item's public import, so no consumer is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.SpaceLineModuleProjInput | T4 | Import the moved definitions; prove the original universal property. |
| Sheaf.TraceFormula.SpaceLineModuleProjMap | unclaimed at inspection | Direct importer; unchanged API, compiled as consumer. |
| Sheaf.TraceFormula.SpaceSectionAlgebraEtaleBaseChange | unclaimed at inspection | Uses SchemeTests, TestLineFamily, testToBase and powerMap; unchanged API, compiled as consumer. |
| Sheaf.AlgebraicGeometry.PolarizedFineLogEtaleDescent | unclaimed at inspection | Text-only sectionMap hit belongs to the log coefficient data; no effect. |


The remaining transitive importers retain the same declarations through the public reexport:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceAmpleLocal | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.CompleteFlagBundle | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ElementaryContractionEvaluation | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.LogCanonicalDeletionAlgebra | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ProjCanonicalMapTwistComparison | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChange | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateGeometry | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateSubschemes | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ProperRelativeAmpleProjectiveBundle | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.QuasiprojectiveQCComposition | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.RelativelyVeryAmple | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.SectionIdealProjExpansion | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.SeparatingPairOpen | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletion | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.VectorProjectivePresentation | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.Paper.LineZeroClassEtaleRealization | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.Paper.LineZeroGeometry | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.Paper.OrgogozoGoodModification | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.Paper.PlurinodalProperHypercover | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.Paper.TraitNearbyBaseChange | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.AmpleNeighbourhood | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.GradedImmersionAmpleCriterion | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.LineQuotientHomogeneousFractionMap | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.PointedGenusZeroProjectiveLine | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.TemkinStableModification | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.ValuationNodalPolarSection | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | not adapted; claim immaterial | Same names, signatures and data via the existing import path. |

## Status

landed 20261023T135412-L-2883719 2026-10-23 (merge of deliver/T4/Sheaf.TraceFormula.SpaceLineModuleProjInput)
