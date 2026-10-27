# AlgebraicGeometry.Etale.RawModuleScalarComparison

## Reason

The item is explicitly listed for retirement in coord/retire-items.tsv, with status DIFFERENT:
the upstream twin has the canonical unit-compatible pullback comparison and generator maps,
but lacks the four historical forget/forget_* names. The current item has zero holes.
Retire its duplicate constructions, retain the compatibility names as abbreviations of the
existing exact coefficient functor, and migrate all twelve current direct imports together.

Final current-source reconciliation, 2026-10-23: the 09:01 UTC quarantine moved
CartierRelativeBoundaryRealization and four prerequisites out of the live library.
Its archived source still imports this item, so the item is now a compatibility
import module publicly importing RawModuleScalarDerivedPullbackIso, with no
declarations or duplicate data. It is not in deleted.txt. Thirteen live consumers
are adapted; the archived H9 consumer is preserved verbatim and is not delivered
or restored. Only RawModuleScalarSourceSquare is withdrawn. The earlier empty
withdrawal and H9 import adaptation below describe the superseded packet.

The canonical upstream comparison is propositionally equal to the old Kan-extension/sheafification
comparison. Both inverse maps have the forgotten module adjunction unit as their abelian transpose.
The compiled scratch regression reconstructs the old map, proves its unit equation and uses
injectivity of the adjunction Hom equivalence to prove equality to the upstream map. freeMap
is definitionally equal. No target changes meaning; targets using the comparison may have
this definitional migration reviewed using that equality. No adopted upstream file is changed.

## Old

The assigned module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ConstantModuleSheavesForgetColimits

/-! # The canonical scalar-forgetting inverse-image comparison

Source: Stacks Project, Tags 03D3 and 03D7.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
namespace RawModuleScalarComparison

/-- Forget scalar operations on a module sheaf.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev forget (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- Scalar forgetting is additive, section by section.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_additive (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (forget Λ X).Additive where
  map_add := by intros; rfl

/-- Scalar forgetting preserves finite limits, as does its presheaf composite.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_preservesFiniteLimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (forget Λ X) := by
  have : PreservesFiniteLimits (forget Λ X ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- Scalar forgetting preserves finite colimits by the constant-coefficient theorem.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_preservesFiniteColimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (forget Λ X) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1} (forget Λ X) :=
    constantModuleSheaves_forget_preservesColimits X Λ
  infer_instance

/-- The canonical Kan-extension and sheafification scalar comparison.
Its construction is the one in `exists_upperStar_forget₂_natIso`, with no choice
of an arbitrary isomorphism. Source: Stacks Project, Tags 03D3 and 03D7.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable def pullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar (ModuleCat.{u + 1} Λ) f ⋙ forget Λ X ≅
      forget Λ Y ⋙ upperStar AddCommGrpCat.{u + 1} f := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let Z := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  have : Z.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (Int.castRingHom Λ)).isLeftAdjoint
  have : (Z ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    inferInstance
  have : U.IsLeftAdjoint :=
    inferInstanceAs (Z ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  have : X.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology U
  let L := (MorphismProperty.Over.pullback @Etale ⊤ f).op
  let P := sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let Q := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let R := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let W := (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj U
  have : U.PreservesLeftKanExtensions L := by
    intro F
    have : U.PreservesPointwiseLeftKanExtension F L := by
      intro c
      let : PreservesColimitsOfShape (CostructuredArrow L c) U :=
        (Adjunction.ofIsLeftAdjoint U).leftAdjoint_preservesColimits.preservesColimitsOfShape
      let : PreservesColimit (CostructuredArrow.proj L c ⋙ F) U :=
        PreservesColimitsOfShape.preservesColimit
      exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit U F L c
    exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise U F L
  let e := sheafComposeNatIso X.smallEtaleTopology U
    (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)
  let e' := U.lanCompIsoOfPreserves L
  change (P ⋙ L.lan ⋙ Q) ⋙ sheafCompose _ U ≅ _
  refine (Functor.associator P (L.lan ⋙ Q) (sheafCompose _ U)) ≪≫ ?_
  refine Functor.isoWhiskerLeft P
    ((Functor.associator L.lan Q (sheafCompose _ U)) ≪≫
      Functor.isoWhiskerLeft L.lan e.symm ≪≫
      (Functor.associator L.lan W R).symm ≪≫
      Functor.isoWhiskerRight e' R) ≪≫ ?_
  exact Iso.refl _

/-- The inverse comparison on a module sheaf.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev pullback (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (pullbackIso Λ f).inv.app G

/-- The free abelian represented sheaf of an etale object.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev freeAbelian (S : Scheme.{u}) (U : S.Etale) :=
  (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)

/-- Send the represented abelian generator to the represented module generator.
Source: Stacks Project, Tag 03FD, the equality of section complexes.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable def freeMap (Λ : Type (u + 1)) [CommRing Λ]
    (S : Scheme.{u}) (U : S.Etale) :
    freeAbelian S U ⟶ (forget Λ S).obj ((freeSheaf Λ S).obj U) := by
  let e : (freeAbelian S U ⟶ (forget Λ S).obj ((freeSheaf Λ S).obj U)) ≃
      ((forget Λ S).obj ((freeSheaf Λ S).obj U)).obj.obj (op U) :=
    ((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free) _).trans
      ((((AddCommGrpCat.adj).whiskerRight S.Etaleᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv)
  exact e.symm ((freeSheafHomEquiv Λ U ((freeSheaf Λ S).obj U)) (𝟙 _))

end RawModuleScalarComparison
end AlgebraicGeometry.Etale
```

Each direct consumer publicly imported
`Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`.
The private scalar_unit proofs in RawModuleScalarSheafComposition and
RawModuleFreeSourceHomBijective expanded that particular Kan/sheafification term.

## New

Replace lean/Sheaf/AlgebraicGeometry/RawModuleScalarPullbackComparison.lean by a
compatibility module with a public import of RawModuleScalarDerivedPullbackIso
and no declarations. The path remains necessary for the quarantined H9 parent.
The existing Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso now publicly imports
WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison and retains the four
historical compatibility names:

```lean
/-- Forget scalar operations on a module sheaf.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev forget (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  moduleAbelianForget Λ X

/-- Scalar forgetting is additive, section by section.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_additive (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (forget Λ X).Additive := moduleAbelianForget_additive Λ X

/-- Scalar forgetting preserves finite limits, as does its presheaf composite.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_preservesFiniteLimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (forget Λ X) := moduleAbelianForget_preservesFiniteLimits Λ X

/-- Scalar forgetting preserves finite colimits by the constant-coefficient theorem.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_preservesFiniteColimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (forget Λ X) := moduleAbelianForget_preservesFiniteColimits Λ X

```

Its derivedPullbackIsoImpl declaration keeps its exact signature and is identified with
its old formula by a proved formula theorem (P2-derived-pullback-reuse.md). The ten other
direct consumers publicly import this existing module. This keeps every old name available
without creating a replacement module or duplicate pullback/free-generator declaration.
The two private scalar_unit proofs are now:

```lean
  change (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
    ((moduleAbelianUpperStarComparison Λ f).app G) = _
  exact Equiv.apply_symm_apply _ _
```

Their obsolete private pullback_unit_hom helpers are removed. All public consumer signatures,
attributes are preserved; the additional canonical reexports are recorded separately. The node for the assigned construction
now points to the canonical upstream declarations and records the unit-characterization route.
The existing derived node records the compatibility names. Mathematical parent dependencies
and the unit route remain intact: no mathematical node is withdrawn.

## Users

The refreshed server preflight also names ParameterRootIntegralNilFibre. Its
`forget` occurrence is `Scheme.ProEt.forget specZ` in the profinite-test
collapse construction, and its `pullback` occurrences are categorical scheme
fibre products. These names do not refer to scalar forgetting. The module is
unclaimed, its statements keep their meaning, and no source adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RootTowerFiniteTensor | unclaimed | Its forget occurrences are CategoryTheory.forget on AddCommGrpCat or CommRingCat, used for sectionwise limits and coefficient maps. They do not denote RawModuleScalarComparison.forget. Its statements and source need no adaptation. |
| Sheaf.Paper.ParameterRootIntegralNilFibre | unclaimed | `Scheme.ProEt.forget specZ` and categorical scheme pullbacks construct profinite-test fibres and their collapse. Neither denotes the scalar comparison. No statement or source adaptation is needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Its forget occurrences are CategoryTheory.forget AddCommGrpCat in the Brown representability argument. They do not denote RawModuleScalarComparison.forget; no source adaptation is needed. |
| Sheaf.Paper.ParameterRootBoundaryData | unclaimed | Its pullback.lift and pullback.fst occurrences construct a categorical scheme fibre product. They do not use the scalar comparison; no source adaptation is needed. |
| Sheaf.Paper.QcqsConstructibleIntegralLatticeTree | A7 | Its pullback occurrences are categorical scheme fibre products and locally free pullback results; its forget occurrence is Mod.forget for condensed module objects. None denotes RawModuleScalarComparison, so no source adaptation is needed. |
| Sheaf.Paper.RelativeProductCoefficientFactorSquares | unclaimed | relativeProductFibreProductIso uses CategoryTheory.Limits.pullback for the Cartesian scheme fibre product. It has no RawModuleScalarComparison occurrence; its pullback match is unrelated to the scalar comparison, and no adaptation is needed. |
| Sheaf.Paper.KummerPartialNerveMorphism | quarantined, unclaimed | Uses the categorical projection pullback.snd in its condensed inverse-image comparison. It does not use the scalar-comparison pullback; archive preserved without adaptation. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Its coefficient_unit field uses CategoryTheory.forget CommRingCat to compare underlying set maps of coefficient-ring sheaves. This is distinct from RawModuleScalarComparison.forget; no source adaptation is needed. |
| Sheaf.Paper.FramedForgetSupport | unclaimed | Uses ordinaryFiniteClass for the underlying supported divisor realization. Its integral-generator and derived-class data are unchanged after expanding the retained forget abbreviation; no source adaptation is needed. |
| Sheaf.Paper.FramedScalarMaps | unclaimed | The divisor splice uses ordinaryFiniteRootMap, whose section maps retain their data definitionally. No scalar comparison is removed from its imported API; no source adaptation is needed. |
| Sheaf.Paper.FramedTransport | unclaimed | Uses ordinaryFiniteRootMap for the cohomological divisor Kummer class; its other pullback references denote geometric or module pullback constructions. The root map remains unchanged on sections, so no source adaptation is needed. |
| Sheaf.Paper.UnitKummerTwoSiteNormalization | unclaimed | Uses RawModuleScalarComparison.forget and pullbackIso for its etale coefficient line, comparison mate and coefficient pullback, and ordinaryFiniteRootMap for the class and naturality equations. The retained forget API has the same data, the canonical pullback comparison is the same unit-compatible map and the root map has the same sections. Its migrated transitive imports provide these names; no source adaptation is needed. |
| Sheaf.Paper.FramedAbelianRealization | unclaimed | divisorRealizeExact is specialized to RawModuleScalarComparison.forget. The compatibility alias retains the moduleAbelianForget functor and exactness instances, so the divisor realization has unchanged data and needs no source adaptation. |
| Sheaf.Paper.FramedIntegralExtension | unclaimed | Its torsor extension maps to E.obj composed with CategoryTheory.forget AddCommGrpCat, rather than the scalar-forgetting functor. No occurrence denotes the retired comparison API; no source adaptation is needed. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | firstProjection and secondProjection use categorical pullback.fst and pullback.snd for the projective-line fibre product. These do not denote the scalar comparison; no source adaptation is needed. |
| Sheaf.Paper.ProjectiveDiagonalComposition | unclaimed | Its pullSectionIso uses the categorical diagonal identity pullback.diagonal_snd for secondProjection. No scalar-comparison construction is referenced; no source adaptation is needed. |
| Sheaf.Paper.RationalP1DiagonalTensor | unclaimed | Uses categorical pullback.condition and pullback.diagonal_fst in the projective-line diagonal tensor square. These are unrelated to RawModuleScalarComparison.pullback; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.RelativeKummerStrictLocalInvariance | unclaimed | The underlying coefficient map uses RawModuleScalarComparison.pullbackIso and forget; relativeKummerClass uses ordinaryFiniteRootMap. The canonical comparison is the same unit-compatible map and the compatibility forget alias retains its data and instances. The root map retains its section maps definitionally. The geometric pullback occurrences denote scheme fibre products. Its imports already obtain the retained API through migrated modules; no source adaptation or statement change is needed. |
| Sheaf.Paper.SmoothPurityStrictCompactificationComparisonRealization | unclaimed | The pullback matches are categorical fibre-product projections and pullback.condition in a compactification base-change comparison. They do not denote the scalar comparison; no source adaptation is needed. |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | unclaimed | Uses categorical scheme fibre products, their projections and pullback.condition in its clopen restriction square. These are distinct from RawModuleScalarComparison.pullback; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.CartierPairTensorAddition | unclaimed | Uses Scheme.Modules.pullback and its monoidal comparison to tensor ordinary module frames. That API is distinct from the retired scalar-comparison API; no source adaptation is needed. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | The pullback occurrences are categorical fibre-product projections and pullback.condition in the clopen base-change square. No occurrence denotes the scalar-comparison API; no source adaptation is needed. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | unclaimed | OpenCompatibility uses VectorIntegrationSite.pullback, the derived etale/pro-etale inverse-image comparison defined in FiniteSiteCoordinates, together with its pullbackUnit. These are distinct from RawModuleScalarComparison.pullback; no source adaptation is needed. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | unclaimed | Uses categorical pullback projections, Over.pullback for geometric base change and WfTensorCompletion.pullback for Frobenius compatibility of completed tensors. These are distinct from the retired comparison API; no source adaptation is needed. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Its section formula uses the underlying point map of the categorical projection pullback.fst. The scalar-forgetting comparison is not used; no source adaptation is needed. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | unclaimed | The pullback occurrence is the constructor of its own RestrictionExpression inductive predicate, indexed by the derived functor pull and its pullSquare. It is unrelated to RawModuleScalarComparison.pullback; no source adaptation is needed. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Uses categorical scheme fibre products, projections, diagonals and pullback.lift in the normal-cone charts and compatibleNormalSplitting. No occurrence denotes the scalar comparison; no source adaptation is needed. |
| Sheaf.Paper.EtaleCartesianTowerTensorComparison | unclaimed | The forget occurrences are explicitly CategoryTheory.forget C in concrete coefficient-category hypotheses. They do not denote the scalar-forgetting comparison; no source adaptation or statement change is needed. |
| Sheaf.Paper.NormAlgclOrderedFiniteModelFiltration | unclaimed | fibreRestriction and ModelCompatible use categorical scheme fibre products, their projections and pullback.condition together with CondensedRing.upperStarComp and pullIso. No occurrence denotes RawModuleScalarComparison.pullback; no source adaptation is needed. |
| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed | fiberModels uses Over.pullback along Spec k. This is scheme base change in an over category, with no scalar-forgetting comparison; no source adaptation or statement change is needed. |
| Sheaf.Paper.TraceStalkCompositorTowerRealization | unclaimed | The pullback occurrences are fields of I.coefficient E, the integral comparison realization data. They do not denote RawModuleScalarComparison.pullback; the tower and stalk compositor statements require no source adaptation. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed | The occurrences are categorical scheme pullbacks, their diagonal, projections and diagonal identities in the normal-cone normalization. No scalar-forgetting comparison is used; no source adaptation is needed. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | RetaggingSectionConclusion uses categorical pullback.fst, pullback.diagonal and pullback.diagonal_fst to express the geometric diagonal. These names are unrelated to the scalar comparison; no source adaptation is needed. |

| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | ProEt.forget lifts maps of schemes to pro-etale objects in returnRestriction and returnRestrictionInverse. It is distinct from RawModuleScalarComparison.forget; no source adaptation is needed. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | CategoryTheory.forget A occurs in the concrete coefficient-category assumptions of the generic tensor transpose. It is distinct from RawModuleScalarComparison.forget; no source adaptation is needed. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | SheafOfModules.forget carries the intrinsic counit to its underlying presheaf. It is distinct from RawModuleScalarComparison.forget; the finite scalar and twist constructions need no source adaptation. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | The pullback occurrences are VectorIntegrationSite.pullback, the derived etale/pro-etale comparison along open charts and frame automorphisms. They do not use RawModuleScalarComparison.pullback; no source adaptation is needed. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | The pullback occurrences denote CategoryTheory.Limits.pullback projections in the geometric Frobenius square. They are distinct from RawModuleScalarComparison.pullback; no source adaptation is needed. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | unclaimed | The pullback occurrences are categorical fibre-product projections, condition and lift equations in the clopen square. They do not use RawModuleScalarComparison.pullback; no source adaptation is needed. |

The latest continuation audit found the newly added direct importer
CartierRelativeBoundaryRealization and migrates its import in this packet.
The current total is twelve direct imports and fourteen adapted modules.
CartierRelativeBoundaryRealization is held by H9; the other thirteen are unclaimed. Its one existing theorem hole is preserved, with no new hole. The
23,498-module audit finds 300 matching consumers, all recorded, and no remaining
direct importer of either withdrawn module. The earlier counts below describe
the earlier audit snapshots.

Exact-import search finds eleven direct users. Every one is adapted in this packet. The table
records downstream declaration users found by the textual search, including its over-approximations,
and the quarantined scalar-forgetting users. The eleven direct importers and two further consumers were unclaimed when the
packet was prepared. The two users named in the return at 92cdd3cfa are included below; neither
requires a source adaptation. A fresh scan of the migrated import graph also found
40 unrelated forget-name matches; their exact meanings are recorded in the table.
The return at head 90fcda2d6 requested six additional pullback-name matches.
All six are now listed, together with 38 further matches from a fresh scan of
all eight retired or relocated names in the current import closure. Each denotes
a different pullback construction, projection or structure field. None requires
an adaptation; the six named modules are unclaimed. The scan includes all current
transitive importers, rather than only the consumers seen by the older packet.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Its forget occurrence is Mon.forget, used to obtain the underlying isomorphism of coefficient monoids. This interface is unchanged and needs no source adaptation. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Its forget occurrences are Mod.forget, used to reflect isomorphisms of coefficient module objects. This interface is unchanged and needs no source adaptation. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryFunctor | unclaimed | Its forget occurrences are CategoryTheory.Mod.forget for condensed coefficient ring objects on the pro-etale site. This interface is unchanged and needs no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization | unclaimed | Its pullback occurrences are categorical scheme fibre products and their projections and diagonals in the affine difference construction. They do not use the scalar comparison; no source adaptation is needed. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed | Its executable pullback occurrence is the categorical projection pullback.snd in the common-stage Frobenius square. Its finite-coefficient comparisons retain the same canonical maps; no source adaptation is needed. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Its pullback occurrences are categorical diagonal morphisms and first projections used for the normal bundle and deformation construction. Their definitions and signatures are unchanged; no source adaptation is needed. |
| Sheaf.Paper.AffineProperSquareStratifiedModule | unclaimed | Its pullback occurrences are categorical scheme fibre products, projections and lifts for the affine proper square. No scalar-comparison declaration is used directly and no source adaptation is needed. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | quarantined, currently unclaimed; H9 at return | Its archived source keeps its original scalar-comparison import verbatim. The item now preserves that path as a compatibility reexport of RawModuleScalarDerivedPullbackIso, so forget and its instances remain available. The root map retains its section data. No consumer edit or restoration is delivered; the earlier H9 forced-adaptation evidence is retained in report.md. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Uses VectorIntegrationSite.pullback to transport the comparison along a scheme isomorphism. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.ContinuousAdicProperBaseChangeRestriction | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Uses Mod.forget to compare the finite coefficient realization with its underlying abelian sheaf. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Uses Mod.forget for the underlying completed restriction and categorical pullback projections in the diagonal diagram. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | Uses Over.forget for a normal-cone isomorphism and categorical pullback projections and diagonals for the deformation chart. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.FiniteModelTopologyComparisonMaps | unclaimed | Uses Mod.forget in the derived comparison with the module topology model. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | Defines its own VectorIntegrationSite.pullback, the derived etale/pro-etale comparison isomorphism. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Uses VectorIntegrationSite.pullback in the derived tensor and inverse-image comparison. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.FiniteSpanModuleDerivedComparison | unclaimed | Uses SheafOfModules.forget, Mod.forget, PresheafOfModules.pullback and categorical pullback projections in the finite-span comparison. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Uses Mod.forget to reflect invertibility of the extension unit. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.IntegralCoefficientSquareNormalization | unclaimed | Uses Mod.forget to transport an isomorphism of coefficient modules to abelian sheaves. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.IntegralQuotientSectionMateRealization | unclaimed | Uses ModuleRingedComparison.pullback in the quotient-extension comparison. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.KummerProductShearHomotopy | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.KummerRefinement | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Defines its own pullback functor for iterates of the local Frobenius. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.NativeIntegralTateTowerLimit | unclaimed | Uses Mod.forget in the underlying integral Tate tower limit. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.OpenSquareSupportScalarCounit | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Uses VectorIntegrationSite.pullback to compare the ordinary trace with its pro-etale realization. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.ProductOpenTensorProjection | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.QlbarBoundedTensorColimit | unclaimed | Defines its own pullback abbreviation for the coefficient-linear inverse-image functor. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.QuotientSectionTensorNormalization | unclaimed | Uses the ringed coefficient pullback functor and its mapDerivedCategoryFactors comparison in the quotient tensor identity. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.SfRationalLocalizationOrthogonality | unclaimed | Uses the pullback field of FrobeniusExchange.models in the completed coefficient realization. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Uses VectorIntegrationSite.pullback in the supported projective Chern comparison. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Uses CategoryTheory.forget CommRingCat in the coefficient-ring realization. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.TraceBoundedQuotientStalkRealization | unclaimed | Uses categorical fibre products and their projections, diagonals or universal maps in its geometric construction. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.SecSmoothPurity.ProEtaleProjectionMateIdentification | unclaimed | Defines RingTransport.pullback and uses that derived ring-transport isomorphism in the projection mate. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Uses Over.forget in the scalar-unit restriction diagram. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Uses a local sheaf-composition forget functor, CategoryTheory.forget and Mod.forget for coefficient module realizations. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | unclaimed | Uses Mod.forget on module sheaves and categorical fibre products and projections for the support intersections. These occurrences do not denote the retired scalar-comparison API; no source adaptation or statement change is needed. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Uses moduleAbelianForget directly for the codomain of ordinaryFiniteRootMap; its textual forget match denotes Scheme.Etale.forget and Over.forget. The retained scalar-forgetting abbreviation denotes that same moduleAbelianForget functor. Its explicit Kummer section formula and statements are unchanged; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Uses CategoryTheory.forget on AddCommGrpCat or ModuleCat, forget₂ for coefficient restriction, and Mod.forget in the classical realization comparison. These are distinct from RawModuleScalarComparison.forget; the classical localizing statements require no source adaptation. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | The pullback matches are the categorical fibre product of the vector-bundle projections and its fst and snd maps in the Fourier kernel and transform. They do not use RawModuleScalarComparison.pullback; no source adaptation or statement change is needed. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | restrictTrace uses VectorIntegrationSite.pullback, the derived etale/pro-etale site comparison, to transport the trace along the affine chart. It does not use RawModuleScalarComparison.pullback; its coefficient, tensor and trace maps require no source adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | Q6 | shiftedLinePullback uses VectorIntegrationSite.pullback to compare the derived site inverse images, followed by comparedLinePullback. This is distinct from RawModuleScalarComparison.pullback; the shifted Tate-line map and statements require no source adaptation. |
| Sheaf.Paper.CondensedOpenSquareScalarComparison | unclaimed | Uses categorical pullback.fst, pullback.snd and pullback.condition in the condensed-coefficient open square and its derived comparison. These do not use RawModuleScalarComparison.pullback; all module comparators, normalization equations and statements are unchanged, so no source adaptation is needed. |
| Sheaf.Paper.ForwardProductCoordinateTransport | unclaimed | Uses categorical pullback objects, projections and lifts to construct middleOpen, middleSquare and productChoice for compactifications. These do not use RawModuleScalarComparison.pullback; all maps and statements are unaffected, and no source adaptation is needed. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | unclaimed | The pullback matches are categorical fibre products of the zero section and transfer projection in TransferConcentration. They do not use RawModuleScalarComparison.pullback; no source adaptation or statement change is needed. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | unclaimed | The pullback.snd, pullback.fst and pullback.condition matches define the categorical base-change square and its projections. They do not use the scalar-comparison API; no source adaptation is needed. |
| Sheaf.Paper.CoordinateGermConcentrationData | unclaimed | The pullback.fst match is the geometric support projection used by transferTwistedCoordinateClass. It is unrelated to RawModuleScalarComparison.pullback; no source adaptation is needed. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | The pullback matches are categorical fibre products and their fst/snd projections on parameter-root towers. CondensedRing.upperStar uses these scheme arrows; no scalar-comparison declaration is used and no source adaptation is needed. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | The forget matches are SheafOfModules.forget in restriction_preserves_tower_limits. They do not denote RawModuleScalarComparison.forget; the restriction/limit normalization and all statements remain unchanged without a source adaptation. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Its local PurityChart.forget is originWitnessFixedAmbient, and its pullback matches are categorical fibre products and projections. Neither denotes the scalar-comparison API; no source adaptation is needed. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Uses IsoAlgebra.forget and Over.pullback for the field operation lifts. Neither denotes the scalar-comparison API; its statements and constructions require no source adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Uses categorical pullback projections and Over.pullback in the identity chart and finite models. It does not use RawModuleScalarComparison.pullback; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.CartierKummerData | unclaimed | CartierKummerChern uses RawModuleScalarComparison.forget to transport the finite-coefficient Ext class. The compatibility abbreviation and its exact-functor instances remain public through the migrated imports and have the same data as moduleAbelianForget. Its statement and normalization are unchanged; no source adaptation is needed. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Textual forget matches denote IsoAlgebra.forget in the Weil-heart and cohomology comparisons; pullback matches denote Over.pullback and categorical pullback.snd for geometric fibres. None denotes the scalar-comparison API, so no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.RawModuleScalarClassMorphisms | unclaimed | New live direct importer: import migrated; its identity functions and freeAbelian source retain the same types and bodies. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison | P2 | Assigned duplicate withdrawn; canonical declarations and four compatibility names retained. |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineLinearActionRigidity | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineLinearTraceAction | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineLinearUniversalAction | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineTraceConstruction | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineTraceLineCounitBaseChange | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineTraceLineLocalization | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineTraceLinePurity | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CartierComplementFrame | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CartierDerivedRealization | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CartierEtaleKummerDerivedUnit | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | quarantined, unclaimed | Archive preserved; restored consumers retain the same compatibility name through the migrated public imports. |
| Sheaf.AlgebraicGeometry.CartierPoleBoundary | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CartierProIntegralDerivedUnit | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CartierProIntegralResidueDerivedUnit | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CartierProIntegralScalar | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CartierProKummerDerivedUnit | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CartierProRootScalar | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CartierReductionData | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Textual pullback matches denote categorical fiber products, their product compactification maps and projections; no scalar-comparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Textual pullback matches denote the product scheme and its two projections in exterior-product realizations; no scalar-comparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.ComparisonConstantGenerator | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.ComparisonForgetScalars | unclaimed | Direct import migrated; signatures preserved. |
| Sheaf.AlgebraicGeometry.Curve.FiniteEtaleCup | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Textual pullback match denotes the fiber-product projection in Pic.map for geometric base change; no scalar-comparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.TraceCupNaturality | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Textual forget match denotes Mon.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleDegreeZeroHom | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.FiniteP1KummerNaturality | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.FiniteP1KummerSplitting | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Textual forget match denotes CategoryTheory.forget on the concrete coefficient category; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T3 | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | W3 | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryEtaleCup | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryEtaleCupFunctoriality | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase | unclaimed | Its integralGenerator_bijective proof uses RawModuleScalarComparison.forget, still supplied through OrdinaryFiniteP1Kummer by the retained definitional alias to moduleAbelianForget; its statement and proof are unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteClassComparison | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteClassInjectivity | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A6 | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer | unclaimed | Public import of this item path kept (reviewer correction: replacing it by ModuleAbelianCoefficientComparison hid RawModuleScalarComparison.forget from Curve.FiniteEtaleCup and the other transitive users listed here); identical adjunction transpose recorded in P2-root-generator-adjunction-transpose.md. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents | unclaimed | The textual pullback hits are categorical fiber products and their diagonal/projection maps, not RawModuleScalarComparison.pullback. No source adaptation is needed; the comparison API remains available through the migrated public imports. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | P4 | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalChernComponents | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalTraceCalculation | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Textual pullback match denotes the categorical pullback.toBase of a supported product; no scalar-comparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | quarantined, unclaimed | Textual pullback matches denote Scheme.Stratification.pullback and fiber-product projections for cover base change; the quarantine archive needs no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap | unclaimed | Reexports the identical canonical construction; see P2-raw-derived-construction-reexports.md. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic | unclaimed | Direct import migrated; signatures preserved. |
| Sheaf.AlgebraicGeometry.RawModuleFreeSourceHomBijective | unclaimed | Direct import migrated; private unit proof uses the upstream defining mate equation; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare | unclaimed | Direct import migrated; signatures preserved. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted | unclaimed | Canonical unshifted theorems reexported with the equal inverse comparison, as recorded in P2-derived-pullback-reuse.md. |
| Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso | unclaimed | Retains the four scalar-forgetting compatibility names; same derived-comparison signature and provably equal formula. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition | unclaimed | Direct import migrated; private unit proof uses the upstream defining mate equation; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors | unclaimed | Reexports the identical canonical construction; see P2-raw-derived-construction-reexports.md. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.ResidueFiniteRootMapIso | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | quarantined, unclaimed | Textual pullback match denotes the categorical projection pullback.snd used for terminal-object evaluation; the quarantine archive needs no adaptation. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Textual forget match denotes MorphismProperty.Over.forget and Over.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.SupportedDerivedUnitForget | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.SupportedIntegralResidueSequence | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.SupportedKummerBoundaryPullback | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.SupportedKummerBoundaryScalar | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.SupportedKummerChernRealization | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarDerived | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarMaps | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarSource | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.AlgebraicGeometry.VectorIntegrationTensorCounit | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Textual forget match denotes SheafOfModules.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.AffineLineSupportGeometry | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Textual forget match denotes Mon.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Textual forget match denotes Mod.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Textual forget match denotes Mod.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Textual forget match denotes Mod.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Textual forget match denotes the concrete forget functor on ModuleCat; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Textual forget match denotes the concrete forget functor on ModuleCat; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Textual forget match denotes the reduction.forget structure field; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Textual forget match denotes CategoryTheory.forget on the concrete coefficient category; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Textual forget match denotes CategoryTheory.forget on CommRingCat; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Textual forget match denotes Over.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Textual forget match denotes CategoryTheory.forget on the concrete coefficient category; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | quarantined, unclaimed | Archive preserved; restored consumers retain the same compatibility name through the migrated public imports. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | Textual pullback matches denote MorphismProperty.Over.pullback on etale/pro-etale objects and their scheme projections; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Textual forget match denotes Mod.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Textual forget match denotes Mod.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Textual forget match denotes IsoAlgebra.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Textual forget match denotes Under.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Textual forget match denotes the concrete forget functor on AddCommGrpCat; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Textual forget match denotes Mod.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Textual pullback matches denote its own integral point-transport functor and compositor; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Textual pullback match denotes DerivedNakayama.pullback on the coefficient tower; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.KummerAdditivity | quarantined, unclaimed | Archive preserved; restored consumers retain the same compatibility name through the migrated public imports. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Textual forget match denotes ProEt.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Textual forget match denotes the concrete forget functor on ModuleCat; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.PurityAffineLineDatum | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Textual pullback matches denote PurityCancellationComparisons.pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Textual pullback match denotes MorphismProperty.Over.pullback on etale objects; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Textual forget match denotes IsoAlgebra.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Textual pullback match denotes the models.pullback structure field for integral systems; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Textual pullback matches denote categorical fiber products and its own FunctorialCupAlgebraPullback field; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | Textual pullback matches denote MorphismProperty.Over.pullback on etale/pro-etale objects; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Textual pullback matches denote the models.pullback structure field for system realizations; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Textual forget match denotes the reduction.forget structure field; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Textual forget match denotes the reduction.forget structure field; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Textual forget match denotes the local Reduction.forget structure field; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Textual forget match denotes IsoAlgebra.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Textual forget match denotes SheafOfModules.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Textual forget match denotes IsoAlgebra.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Textual forget match denotes CategoryTheory.forget on the concrete coefficient category; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Textual forget match denotes Over.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed | Transitive consumer; compatibility names retained and comparison unchanged as a morphism. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Textual forget match denotes SheafOfModules.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Textual forget match denotes Mod.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Textual pullback matches denote categorical fiber products, their projections or site base change; no scalar-comparison API use or source adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Textual forget match denotes Mod.forget; no RawModuleScalarComparison API use or source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Textual forget match denotes Mod.forget and Over.forget; no RawModuleScalarComparison API use or source adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Textual forget match denotes the separately defined WeilBoundedConstructible.forget; no RawModuleScalarComparison API use or source adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Textual forget match denotes WeilBoundedConstructible.forget; no RawModuleScalarComparison API use or source adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Textual forget match denotes WeilBoundedConstructible.forget and IsoAlgebra.forget; no RawModuleScalarComparison API use or source adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Textual forget match denotes WeilBoundedConstructible.forget; no RawModuleScalarComparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Textual pullback matches denote categorical fiber products and their projections in supported Kunneth; no scalar-comparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization | unclaimed | Textual pullback matches denote categorical fiber products and projections in constant support exchange; no scalar-comparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | unclaimed | Textual pullback matches denote the product scheme and its projections for full-support products; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SectionCentredChartData | unclaimed | Textual pullback matches denote scheme fiber products and projections in the section-centred chart data; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SectionLocalDualizingComparisons | unclaimed | Textual forget match denotes CategoryTheory.forget on ModuleCat, and pullback matches denote scheme fiber products and projections; no scalar-comparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Textual pullback matches denote SignedFiniteTateComparison.pullback and categorical pullback.snd for support restriction; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | Textual pullback matches denote categorical pullback.lift and pullback.lift_snd in the common-open section arrow; no scalar-comparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps | unclaimed | Textual pullback match denotes MorphismProperty.Over.pullback on etale objects; no scalar-comparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Textual pullback matches denote scheme fibre products over residue-field points; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Textual pullback match denotes DerivedNakayama.pullback on integral complexes; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Textual pullback matches denote scheme fibre products and pullback.fst in pro-etale cohomology; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Textual pullback matches denote categorical pullback.snd for relative support and restriction maps; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.IntegralBoundedStratumBaseChange | Y3 | Textual pullback matches denote the module's own termwise exact module pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.DerivedOpenSquareRestriction | unclaimed | Textual pullback matches denote categorical pullback.fst, pullback.snd and pullback.condition in the open-square comparison; no scalar-comparison API use or source adaptation. |

| Sheaf.AlgebraicGeometry.FiniteRootSiteComparison | unclaimed | Uses MorphismProperty.Over.pullback and categorical scheme projections in site and units maps; no scalar-comparison API use or source adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | quarantined, unclaimed | Uses a scheme pullback projection and the models pullback realization field; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.AffineCurveHcZero | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | quarantined, unclaimed | The pullback occurrence declares the local realization comparison field; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | quarantined, unclaimed | Uses the FrobeniusExchange.models pullback realization field; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | quarantined, unclaimed | Uses scheme pullback projections and the models pullback comparison; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | quarantined, unclaimed | The pullback occurrence declares the local realization comparison field; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FiniteProductCompactification | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FourierKernelConvolution | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | quarantined, unclaimed | Uses IsoAlgebra.forget and categorical pullback projections; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | quarantined, unclaimed | Uses the ReductionPull comparison structure field pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.MateOpenRestriction | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ProperHeartBound | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | quarantined, unclaimed | Uses the models pullback realization field; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | quarantined, unclaimed | Uses MorphismProperty.Over.pullback on weakly etale objects; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | quarantined, unclaimed | Uses CategoryTheory.forget C and categorical pullback projections and diagonals; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.PurityFrameIndependence | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | unclaimed | Uses Under.forget E in the coefficient indexing functor; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.RegularImmersionPurity | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.SupportedAffineLineHomotopy | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.TowerClassPullback | quarantined, unclaimed | Uses MorphismProperty.Over.pullback and the categorical scheme projection; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.TraceFixedScheme | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.TwConventions | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.VectorBundleThomClass | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | quarantined, unclaimed | Defines its own pullback abbreviation for pbcIsoIntegralPullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | quarantined, U1 | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | quarantined, unclaimed | Uses the local framework S.pullback finite comparison field; no scalar-comparison API use or source adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | quarantined, unclaimed | Uses categorical fibre products, their projections or the associated over-site pullback; no scalar-comparison API use or source adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | quarantined, unclaimed | Uses IsoAlgebra.forget in the Weil-object trace; no scalar-comparison API use or source adaptation. |

There is no rework row for the assigned item. The P2 return at head 92cdd3cfa requested the
OrdinaryFiniteClassArbitraryBase and ProEtaleP1DiagonalComponents rows above. This repair adds
both, records their actual uses, and preserves the retained Lean changes against current source.
The subsequent return at head 90fcda2d6 requested CompactProductArrows,
CompactProductRealizationArrows, Curve.KummerJacobianTateModule,
ProperSupportCompactMaps, PullbackConstantModelConstructible and
RetractedSupportLocalizationComparison. Their code uses categorical pullbacks
(and Scheme.Stratification.pullback in PullbackConstantModelConstructible), not
the retired scalar-comparison declaration. All six rows and the additional
38 current textual matches have been added without source changes.
The current rework table places PullbackConstantModelConstructible and
RetractedSupportLocalizationComparison in quarantine; both archives have been
read and their rows record that status. Neither archive imports the retired
module directly or uses its scalar-comparison declarations.
A complete interface-name scan following the refreshed preflight additionally
found KunnethSupported, SupportedConstantExchangeNormalization,
SupportedFullSupportProduct, SectionCentredChartData and
SectionLocalDualizingComparisons. The rows above record their unrelated
categorical pullbacks and concrete forget functor. No source adaptation is needed.
The return at head aee84b65b requested SupportedBottomGluing and
IdentityOpenDerivedRestriction. Their rows above record the gluing structure's
pullback field and categorical fibre-product maps, respectively. Both modules
are currently unclaimed; neither uses the scalar-comparison pullback or needs
a source adaptation.
The refreshed downstream scan also found OrdinaryFiniteP1DecompositionMaps,
ProperHeartBoundRational, IntegralTensorProduct, ProperHeartBoundLattice and
RelativeSupportBottomDescent. Their rows record the distinct site pullback,
scheme fibre products, integral-complex pullback and support projections.
All five are unclaimed and need no source adaptation.
The complete changed-interface audit additionally found
IntegralBoundedStratumBaseChange (held by Y3) and DerivedOpenSquareRestriction
(unclaimed). Their rows distinguish the local module pullback and categorical
pullback projections from the scalar-comparison API. Neither is adapted.
The quarantine files and their Lean attachments/dependencies remain untouched. The unit
sk-lem-failure-field has empty realized.statement and realized.steps; its mathematical route is
unchanged. Parent nodes retain their references to the comparison node, now attached upstream.

The return at head 7973c84dc identified CartierKummerData and
ImmersionWeilPullbackLocalBehavior as missing Users rows. Both current modules
have been read and are unclaimed. CartierKummerData uses the retained forget
abbreviation in CartierKummerChern; its Ext normalization therefore keeps the
same scalar-forgetting functor and instances. ImmersionWeilPullbackLocalBehavior
instead uses IsoAlgebra.forget, Over.pullback and categorical pullback.snd.
Their individual rows above record these effects. Neither requires a Lean edit.
The retained implementation was compared with the current shared source;
deliver3.py rebuilds the repaired packet on the freshly fetched sheaf-dag base.

The return at head 9c8dbd89f requested five further individual Users rows:
ConcentratedSupportEtaleTransfer, CoordinateGermCohomologyClasses,
CoordinateGermConcentrationData, RootTowerLisseMorphismExtension and
SemilinearCompactSupportCoefficientTransport. Each current source was read and
checked against the claims directory; all five are unclaimed. Their rows above
distinguish categorical pullbacks and SheafOfModules.forget from the retired
scalar-comparison declarations. None requires a Lean edit.

The 2026-10-22 current-source audit also includes the replacement import graph and
all preserved quarantine archives. It adds the individual consumer rows above,
including FiniteRootSiteComparison, QlbarInternalHomCoefficientComparison and
TameRootTowerExtension. Quarantined files and their node attachments remain
untouched. Their unrelated pullback/forget matches require no source edits.
The three further genuine Kummer consumers are recorded separately in
P2-root-generator-adjunction-transpose.md.

The resumed 2026-10-22 audit reads 22,093 live and quarantined modules and finds
255 matching consumer modules across the original and migrated import graphs.
The three new rows above cover the additional matches. Their current sources
and claims were checked; all three are unclaimed and need no Lean edit.
Every matching consumer has a Users entry, and neither withdrawn module has
a remaining direct importer in the migrated graph.

The repair of the return at head 5b0e73df3 adds all six requested consumer
records, with the two genuine root-map consumers also in the root-generator
record. The refreshed audit reads 23,417 live and preserved quarantined modules
and finds 298 matching modules across the original and migrated import graphs.
It records 45 further textual matches above, each checked in its current source;
all are unclaimed and use other functors, structure fields or categorical fibre
products. No source adaptation is required. The migrated graph has no direct
importer of either withdrawn module. The delivery tool rebases the retained
packet onto its freshly fetched base; no adopted source file is changed.

The continuation audit reads 23,432 live and quarantined source modules and finds
299 matching consumers. ForwardProductCoordinateTransport is now recorded above;
its matches denote categorical fibre products. AffineSpacePurityComparison is
currently held by Q6, and its holder is updated above. Neither module needs a
Lean edit. All thirteen retained adapted modules are unclaimed. No migrated
importer refers to either withdrawn module.

The 2026-10-23 landing-repair refresh checks 23,779 live and quarantined sources
across both import graphs. All 321 matching consumers are recorded or adapted,
including each of the six consumers named in the earlier return and the new
ExceptionalInverseImageExistence and LocalizedDirectImageComparison matches.
Their occurrences denote Mon.forget and Mod.forget, respectively. No migrated source
imports either withdrawn module. Of the fourteen adapted modules,
CartierRelativeBoundaryRealization is held by H9 and the other thirteen are
unclaimed. AffineSpacePurityComparison remains held by Q6 and needs no source edit.
The fresh repair audit rechecked each of the six returned consumer occurrences
and their holders. All changed node copies differ from current source only in
the permitted fields, and their proof_deps agree with their proof-step uses.

The return at head c4917322e6a identifies H9 as the current holder of
Sheaf.Paper.CartierRelativeBoundaryRealization. Its only adapted line is line 12:
the public import of the withdrawn RawModuleScalarPullbackComparison is replaced
by RawModuleScalarDerivedPullbackIso, which supplies the same retained forget API.
The original consumer compiled against the changed dependencies and empty
withdrawal modules fails at 112:4 with the unknown identifier
`RawModuleScalarComparison.forget`, then reports dependent unknown identifiers
and a kernel unknown-constant error. The replacement import restores the
retained compatibility API. The exact diagnostics and one-line import diff are
recorded in report.md under `## Forced adaptations`. The adapted file compiles
against the same setup (exit code 0, no diagnostics, 20.1 seconds). This migration
is required by the retirement; no declaration, signature, visibility, definition
body or proof of H9's module changes.

The final resumed source audit covers 23,801 live and quarantined modules and
still finds 321 matching consumers, all recorded or adapted, with no remaining
importers of either withdrawal. The current claim record still names H9, and
the exact one-line consumer diff above is unchanged. All fourteen packet modules
compile successfully with no diagnostics through the project-server backend.

The final quarantine reconciliation supersedes the earlier fourteen-module adaptation counts and empty-item withdrawal instructions: the packet has the item compatibility module and thirteen adapted live modules, no H9 source file, zero holes and only the SourceSquare withdrawal. All archives and their Lean/DAG attachments are preserved.

## Status

landed 20261024T015347-L-2367834 2026-10-24 (merge of deliver/P2/Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison)
