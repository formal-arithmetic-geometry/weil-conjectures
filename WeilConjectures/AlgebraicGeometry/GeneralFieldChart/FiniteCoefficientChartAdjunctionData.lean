/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.AlgebraicGeometry.FiniteAffineRightScalarNormalForm
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCtfFunctors
import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionData
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude

/-! # Counit-pinned chart realization over a general characteristic-p field

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data).

The output chart isomorphism is constructed by right-adjoint uniqueness from the
ordinary summation/ordered affine adjunction. The realization record retains the
actual transported counit. Scalar transport uses the exact restriction square and
actual derived scalar-extension adjunctions; it uses no normalized-tower model.
-/

public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.GeneralFieldChart

/-- Reuse the recorded finite-ctf predicate without reexporting its legacy import
closure. This is exactly `spFiniteConstructibleTor`, with no alternate Tor or
constructibility definition. Source: the finite-ctf domain of chart realization.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartCtf (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory T A) :=
  AlgebraicGeometry.ProEtale.spFiniteConstructibleTor T A

/-- The full subcategory of the recorded finite-ctf objects.
Source: chart realization, finite-ctf domain.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
abbrev chartCtfCategory (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :=
  (chartCtf T A).FullSubcategory

/-- The recorded actual derived tensor, exposed through its ordinary finite-ring
signature. The data is the existing `scalarExtensionFunctor`, not a chosen tensor model.
Source: chart realization, coefficient extension.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartScalar {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    proEtaleDerivedCategory T A ⥤ proEtaleDerivedCategory T B :=
  AlgebraicGeometry.ProEtale.scalarExtensionFunctor φ T

/-- The recorded exact derived scalar restriction.
Source: chart realization, normalized coefficient adjunction.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartRestrict {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    proEtaleDerivedCategory T B ⥤ proEtaleDerivedCategory T A :=
  AlgebraicGeometry.ProEtale.scalarRestriction φ T

/-- The coefficient-independent compactification's actual compact-support functor.
Source: chart realization, chosen compactification.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartCompact (A : Type u) [CommRing A] [Finite A] {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory Y A :=
  AlgebraicGeometry.ProEtale.reductionCompactSupport A j p

/-- The restriction of precisely the recorded compact-support functor to the full
finite-ctf domains. Source: chart realization, constructible adjunction.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
@[expose] def chartCtfCompact (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (hF : ∀ M : chartCtfCategory X A, chartCtf Y A ((chartCompact A j p).obj M.obj)) :=
  (chartCtf Y A).lift ((chartCtf X A).ι ⋙ chartCompact A j p) hF

/-- The full-subcategory restriction of the recorded coefficient extension.
Source: chart realization, finite-ctf scalar domain.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
@[expose] def chartCtfScalar {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (hT : ∀ M : chartCtfCategory T A, chartCtf T B ((chartScalar φ T).obj M.obj)) :=
  (chartCtf T B).lift ((chartCtf T A).ι ⋙ chartScalar φ T) hT

/-- The recorded compact-support coefficient map, with its exact original components.
Source: def-sp-reduction-direct-image-comparison, as used in chart realization.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartCompactScalarComparison {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    chartCompact A j p ⋙ chartScalar φ Y ⟶ chartScalar φ X ⋙ chartCompact B j p :=
  AlgebraicGeometry.ProEtale.reductionDirectImageComparison φ j p

/-- The actual scalar/pullback comparison, through the same ordinary finite-ring
signature. Source: chart realization, inverse image and scalar compatibility.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartScalarPullbackIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U Y : Scheme.{u}} (g : U ⟶ Y) :
    chartScalar φ Y ⋙ proEtaleConstantRingDerivedPullback B g ≅
      proEtaleConstantRingDerivedPullback A g ⋙ chartScalar φ U :=
  AlgebraicGeometry.ProEtale.directImageScalarPullbackIso φ g

/-- The existing ordinary-etale pullback/Tate/shift chart operation, with its actual data.
Source: chart realization, displayed right normal form.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartEtaleOperation (R : Type (u + 1)) [CommRing R] (N : ℕ) (hR : (N : R) = 0)
    {U Y : Scheme.{u}} (g : U ⟶ Y) (a : ℕ) (b : ℤ) :
    Etale.DerivedCategoryModule R Y ⥤ Etale.DerivedCategoryModule R U :=
  AdjunctionTransfer.etaleChartOperation R N hR g a b

/-- The existing ordinary pro-etale pullback/Tate/shift operation. Its Tate line is
comparison pullback of the finite etale Tate line. Source: chart realization.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartProOperation (R : Type (u + 1)) [CommRing R] (N : ℕ) (hR : (N : R) = 0)
    {U Y : Scheme.{u}} (g : U ⟶ Y) (a : ℕ) (b : ℤ) :
    DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)) :=
  AdjunctionTransfer.proEtaleChartOperation R N hR g a b

/-- The specified exact site comparison for the chart operation.
Source: chart realization, pullback/tensor/shift transport.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartOperationIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hR : (N : R) = 0) {U Y : Scheme.{u}} (g : U ⟶ Y) (a : ℕ) (b : ℤ) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory ⋙
        chartProOperation R N hR g a b ≅
      chartEtaleOperation R N hR g a b ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory :=
  AdjunctionTransfer.chartOperationComparison R N hR g a b

/-- The ordinary-etale scalar extension appearing in the same site square.
Source: chart realization, ordinary finite-ctf scalar domain.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartEtaleScalar {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T ⥤
      Etale.DerivedCategoryModule (ULift.{u + 1, u} B) T :=
  CoefficientScalarRepresentatives.extension T.smallEtaleTopology
    (RingHom.ulift.{u + 1, u + 1, u, u} φ)

/-- K-flat preservation for the displayed scalar map, supplied by the existing
extension construction with its induced algebra structure. Source: Stacks 06YY.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
instance chartFixedScalarKFlat {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (sheafExtendScalars φ T).PreservesKFlatQuasiIso :=
  AlgebraicGeometry.ProEtale.chartScalarPreservesKFlat φ T

/-- Fix the existing small pro-etale site at its object universe.
Source: the small-site convention in the chart realization node.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
instance chartProEtaleSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0} _

/-- Canonical realization of the chosen compact-support functor, obtained by cancelling
the realization equivalences at the open factor and then using the specified
K-injective direct-image comparison. Every comparison is fixed on sections. The ringed
and fixed constant direct images are identified by the published, proved equality
`reductionConstantPush_eq` (scalar adjunction triangle identity); no new proof is made.
Source: blueprint Charts, site realization
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartCompactSupportFixedIso (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ chartCompact A j p ≅
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        j).mapDerivedCategory ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor :=
  Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence X A).functor
      (Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero j A).mapDerivedCategory
        (eqToIso (reductionConstantPush_eq A p))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          ((sfIntrinsicModuleEquivalence X A).funInvIdAssoc
            (ProEtale.openImmersionLowerShriek
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
                (sfIntrinsicModuleEquivalence Z A).functor)) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        j).mapDerivedCategory (sfIntrinsicDerivedDirectImageComparison p A)

/-- The recorded finite-coefficient site inverse image followed by canonical realization.
This composite uses the recorded site and scalar-extension functors.
Source: blueprint Charts, site realization
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
@[expose] def chartSite (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence T A).functor

/-- The compact-support comparison in the original intrinsic categories, with its
proper counit mate and the recorded realization normalization.
Source: blueprint Charts, site realization
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartSiteCompactSupportIso (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    [IsProper p] :
    DerivedCategory.Plus.ι ⋙ chartSite A X ⋙ chartCompact A j p ≅
      DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⋙
            chartSite A Y :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (chartCompactSupportFixedIso A j p) ≪≫
      (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (fixedCompactSupportComparisonIso (ULift.{u + 1, u} A)
        (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))) _ ≪≫
    Functor.associator _ _ _


/-- The ordered affine-space left functor compared with a specified compactification.
Every factor is the published proper/open composition or common-refinement comparison.
The identity step uses the two exact identity functors, so no orientation is chosen.
Source: Charts, compactification composition and refinement; node proof Step 4
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartEtaleAffineLeftIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    (c : Compactification (affineTraceProjection S d)) →
    Etale.affineTraceLeft A S d ≅
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Nat.rec (motive := fun n ↦ ∀ c : Compactification (affineTraceProjection S n),
      Etale.affineTraceLeft A S n ≅
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun c ↦
      (Functor.isoWhiskerRight
          (Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ Etale.rightDerivedLowerStarIdIso A S).symm ≪≫
        Etale.rightDerivedLowerShriekOfCompactificationIso A
          (Compactification.ofIsProper (𝟙 S)) c)
    (fun n ih c ↦
      let cp := HasCompactification.compactification (affineTraceProjection S n)
      let ce := c.ofComp cp
      Functor.isoWhiskerRight
          (Etale.rightDerivedLowerShriekOfCompactificationIso A
            (affineTraceLineCompactification (affineTraceTower S n)) ce.restrict) _ ≪≫
        Functor.isoWhiskerLeft _ (ih cp) ≪≫
        Etale.rightDerivedLowerShriekOfCompactificationCompIso A cp ce ≪≫
        Etale.rightDerivedLowerShriekOfCompactificationIso A (cp.comp ce) c) d

/-- The chart right adjunction is literally sum/evaluation followed by the specified
ordered affine-space adjunction. The inverse-image model comparison is the canonical
exact-to-left-derived comparison.
Source: Charts, sum followed by ordered affine trace; node proof Step 4
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartEtaleChartAdjunction (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) [IsNoetherian S] (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT)
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    {U : Scheme.{u}} (e : U ⟶ affineTraceTower S d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        Etale.affineTraceLeft A S d ⊣
      Etale.affineTraceRight A N hA S d ⋙ Etale.ordinaryFinitePullback A e :=
  ((Etale.derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).ofNatIsoRight
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm).comp
      (Etale.affineTraceAdjunction A N hA t D S hS d)

/-- Canonical chart left comparison: graph-normalized sum extension, ordered affine
composition, common refinement, then inverse source-open comparison.
Source: Charts, the normalized left chart comparison; node proof Step 4
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartEtaleChartLeftIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : Etale.EtaleCompactSupportNormalization A)
    {X S U : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian U]
    (f : X ⟶ S) (i : U ⟶ X) [IsOpenImmersion i]
    (d : ℕ) (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    (he : i ≫ f = e ≫ affineTraceProjection S d)
    (cf : Compactification f) :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        Etale.affineTraceLeft A S d ≅
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) i inferInstance).mapDerivedCategory ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf :=
  letI := affineTraceNoetherian S d
  let cp := HasCompactification.compactification (affineTraceProjection S d)
  let cg := HasCompactification.compactification (e ≫ affineTraceProjection S d)
  Functor.isoWhiskerLeft _ (chartEtaleAffineLeftIso A S d cp) ≪≫
    Etale.etaleAmbientLeftComparison A M e (affineTraceProjection S d) cp cg ≪≫
    (Etale.etaleAmbientLeftComparison A M i f cf (cg.copy he)).symm

/-- The chart identification is the unique counit-preserving right-adjoint comparison
for the preceding left comparison. It is therefore normalized by actual affine trace
and summation over e, with no free scalar or arbitrary right-functor isomorphism.
Source: Charts, counit-preserving right-adjoint uniqueness; node proof Step 4
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartEtaleChartRightIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : Etale.EtaleCompactSupportNormalization A)
    {X S U : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian U]
    (f : X ⟶ S) (i : U ⟶ X) [IsOpenImmersion i]
    (d : ℕ) (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ f = e ≫ affineTraceProjection S d) (cf : Compactification f)
    (G : Etale.DerivedCategoryModule A S ⥤ Etale.DerivedCategoryModule A X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ⊣ G)
    (N : ℕ) (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT) (hS : IsUnit (N : Γ(S, ⊤))) :
    G ⋙ Etale.ordinaryFinitePullback A i ≅
      Etale.affineTraceRight A N hA S d ⋙ Etale.ordinaryFinitePullback A e :=
  (((Etale.derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) i inferInstance).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i).symm).comp
        adj).rightAdjointUniq
    ((chartEtaleChartAdjunction A S N hA t D hS d e).ofNatIsoLeft
      (chartEtaleChartLeftIso A M f i d e he cf))

/-- Canonical realization/pullback comparison, preserving the actual pullback units.
Source: blueprint Charts, site realization
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartRealizationPullbackIso (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (i : U ⟶ X) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ proEtaleConstantRingDerivedPullback A i ≅
      sfFixedDerivedPullback A i ⋙ (sfIntrinsicDerivedEquivalence U A).functor :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).functor
          (openSquarePullbackModel A i) ≪≫
        (sfIntrinsicModuleEquivalence X A).funInvIdAssoc
          (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i ⋙
            (sfIntrinsicModuleEquivalence U A).functor)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Exact site/pullback comparison, followed by canonical coefficient realization.
Source: blueprint Charts, site realization
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartSitePullbackIso (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (i : U ⟶ X) :
    chartSite A X ⋙ proEtaleConstantRingDerivedPullback A i ≅
      Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) i ⋙ chartSite A U :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (chartRealizationPullbackIso A i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sfDerivedComparisonPullbackIso A i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).symm _

/-- The precise transported counit equation in intrinsic coordinates.
Factoring this proposition keeps the realization record's projections small.
Source: blueprint Charts, site realization
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartRealizationCounitEquation (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hF : ∀ M : chartCtfCategory X A,
      chartCtf Y A ((chartCompact A j p).obj M.obj))
    (G : chartCtfCategory Y A ⥤ chartCtfCategory X A)
    (adj : chartCtfCompact A j p hF ⊣ G)
    (origin : chartCtfCategory Y A ⥤
      Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y)
    (originIso : origin ⋙ chartSite A Y ≅ (chartCtf Y A).ι)
    (right : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y ⥤
      Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
    (adjunction : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⊣ right)
    (right_plus : ∀ K, DerivedCategory.TStructure.t.plus (right.obj (origin.obj K)))
    (rightIso : G ⋙ (chartCtf X A).ι ≅
      origin ⋙ right ⋙ chartSite A X) : Prop :=
  ∀ K : chartCtfCategory Y A,
    (chartCompact A j p).map (rightIso.hom.app K) ≫
      (chartSiteCompactSupportIso A j p).hom.app
        ⟨right.obj (origin.obj K), right_plus K⟩ ≫
      (chartSite A Y).map (adjunction.counit.app (origin.obj K)) ≫
      originIso.hom.app K = (adj.counit.app K).hom

/-- A constructible exceptional adjunction realized on the ordinary etale site.
The input origin and output comparison are natural isomorphisms. The final equation
fixes the output comparison by the actual compact-support and ordinary counits.
Thus neither a free map nor an ambient pro-etale adjunction is assumed.
Source: Charts, transported ordinary adjunction; node proof Step 3
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
structure ChartAdjunctionRealization (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hF : ∀ M : chartCtfCategory X A,
      chartCtf Y A ((chartCompact A j p).obj M.obj))
    (G : chartCtfCategory Y A ⥤ chartCtfCategory X A)
    (adj : chartCtfCompact A j p hF ⊣ G) where
  /-- An ordinary-etale origin of every Dctf input. -/
  origin : chartCtfCategory Y A ⥤
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y
  /-- The origin is bounded constructible of finite Tor amplitude. -/
  origin_ctf : ∀ K, Etale.DerivedCategory.boundedConstructibleFiniteTor
    (ULift.{u + 1, u} A) Y (origin.obj K)
  /-- The origin recovers exactly the original intrinsic object. -/
  originIso : origin ⋙ chartSite A Y ≅ (chartCtf Y A).ι
  /-- The ordinary right adjoint for the identical fixed compactification. -/
  right : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y ⥤
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X
  /-- Its actual ordinary-etale adjunction. -/
  adjunction : Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⊣ right
  /-- The ordinary right functor preserves the finite-ctf comparison domain. -/
  right_ctf : ∀ K, Etale.DerivedCategory.boundedConstructibleFiniteTor
    (ULift.{u + 1, u} A) X (right.obj (origin.obj K))
  /-- Its values on the origins lie in the bounded-below comparison domain. -/
  right_plus : ∀ K, DerivedCategory.TStructure.t.plus (right.obj (origin.obj K))
  /-- The exceptional output comparison. -/
  rightIso : G ⋙ (chartCtf X A).ι ≅ origin ⋙ right ⋙ chartSite A X
  /-- The output comparison retains the actual transported counit. -/
  counit : chartRealizationCounitEquation A j p hF G adj
    origin originIso right adjunction right_plus rightIso

/-- The intrinsic chart identification, normalized by ordinary sum/evaluation and the
specified affine-space trace. All changes of sites, scalars and inverse image are the
canonical comparisons defined above. No orientation of a Tate line is chosen.
Source: Charts, site transport and the coordinate right adjunction; node proof Steps 3--4
(blueprint: def-pur-finite-coefficient-chart-adjunction-data).
-/
def chartIntrinsicChartIso (A : Type u) [CommRing A] [Finite A]
    {X Z Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hF : ∀ M : chartCtfCategory X A,
      chartCtf Y A ((chartCompact A j p).obj M.obj))
    (G : chartCtfCategory Y A ⥤ chartCtfCategory X A)
    (adj : chartCtfCompact A j p hF ⊣ G)
    (R : ChartAdjunctionRealization A j p hF G adj)
    (M : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} A))
    (i : U ⟶ X) [IsOpenImmersion i] (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ (j ≫ p) = e ≫ affineTraceProjection Y d)
    (N : ℕ) (hA : (N : ULift.{u + 1, u} A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} A) N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} A) N hA t T hT)
    (hY : IsUnit (N : Γ(Y, ⊤))) (K : chartCtfCategory Y A) :
    (proEtaleConstantRingDerivedPullback A i).obj (G.obj K).obj ≅
      (chartSite A U).obj
        ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) e).obj
          ((Etale.affineTraceRight (ULift.{u + 1, u} A) N hA Y d).obj (R.origin.obj K))) :=
  (proEtaleConstantRingDerivedPullback A i).mapIso (R.rightIso.app K) ≪≫
    (chartSitePullbackIso A i).app _ ≪≫
    (chartSite A U).mapIso
      ((chartEtaleChartRightIso (ULift.{u + 1, u} A) M (j ≫ p) i d e he
        (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))
        R.right R.adjunction N hA t D hY).app (R.origin.obj K))

open AlgebraicGeometry.Etale

/-- Expand the identity normal form at zero into its canonical pullback, Tate-unit
and zero-shift presentation; positive dimensions already have that presentation.
Source: Charts, zero-coordinate units
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartExpandOrderedIso
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) : (d : ℕ) →
    orderedAffineRight A N hA S d ≅
      ordinaryFinitePullback A (affineTraceProjection S d) ⋙
        Etale.derivedTensorRight (ModuleCat.{u + 1} A) (affineTraceTower S d)
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist (affineTraceTower S d) N A hA d)) ⋙
        shiftFunctor _ (2 * (d : ℤ))
  | 0 =>
      (Functor.isoWhiskerRight (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫
        Functor.isoWhiskerRight
          ((Etale.derivedTensorRightFunctor (ModuleCat.{u + 1} A) S).mapIso
            (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S) ≪≫
              Etale.derivedTensorRightUnitorNatIso (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ shiftFunctorZero _ ℤ).symm
  | _ + 1 => Iso.refl _

/-- Expand the prescribed tower normal form and restrict it to a chart. The ordered
Tate pullback is followed by the canonical symmetry converting to the chart operation's
left-Tate convention. Source: Charts, ordered normal form and chart restriction
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartEtaleNormalIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) {U : Scheme.{u}} (e : U ⟶ affineTraceTower S d)
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A e).obj ((affineTraceRight A N hA S d).obj K) ≅
      (chartEtaleOperation A N hA
        (e ≫ affineTraceProjection S d) d (2 * (d : ℤ))).obj K :=
  (ordinaryFinitePullback A e).mapIso
      (((orderedAffineRightIso A N hN hA S hS d).app K) ≪≫
        (chartExpandOrderedIso A N hA S d).app K) ≪≫
    (Etale.tensorEPullback (ModuleCat.{u + 1} A) N
      (fun X r ↦ Scheme.finiteEtaleTateSheaf A N X hA (r : ℤ))
      (fun f hX r ↦ (Scheme.finiteEtaleTwistPullbackData A N hN hA).c f hX
        (affineTracePullbackInvertible N f hX) r)
      e (affineTraceInvertible N S hS d) d (2 * (d : ℤ))).app
        ((ordinaryFinitePullback A (affineTraceProjection S d)).obj K) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((Etale.derivedTensorRight (ModuleCat.{u + 1} A) U
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist U N A hA d))).mapIso
          ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e
            (affineTraceProjection S d)).symm.app K) ≪≫
        ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) U).app
          ((ordinaryFinitePullback A (e ≫ affineTraceProjection S d)).obj K)).app
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist U N A hA d)) ≪≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} A) U).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist U N A hA d))).mapIso
              ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
                (e ≫ affineTraceProjection S d)).app K))


set_option maxHeartbeats 1000000 in
-- Checking definitional equality with the published universal pair expands its choice data.
/-- The actual derived tensor adjunction, obtained from the generic ringed-site theorem
with its tensor-unit normalization on K-flat representatives. The ordinary functor and
derived universal pair are definitionally the recorded scalar functor's pair; no second
scalar functor is chosen. Source: Stacks 07A6, chart scalar transport.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartScalarAdjunction {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    chartScalar φ T ⊣ chartRestrict φ T := by
  letI : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let ρ : proEtaleConstantRing T A ⟶ proEtaleConstantRing T B :=
    proEtaleConstantRingMap (T := T) φ
  let D := SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u} ρ
  let E := D.choose
  let h := D.choose_spec.choose
  letI := D.choose_spec.choose_spec.choose_spec.choose
  let hc :=
    (SheafOfModules.sheafRingDerivedCoefficientAdjunction.{u + 2, u + 1, u + 1, u}
      ρ).choose_spec.choose_spec
  let a := hc E h (fun f ↦ D.choose_spec.choose_spec.choose f)
  let ld := D.choose_spec.choose_spec.choose_spec.choose_spec.2.2
  exact (a.choose_spec.2 ld.choose ld.choose_spec.choose
    ld.choose_spec.choose_spec.1).choose

/-- The exact restriction square between intrinsic and fixed constant-module sheaves,
localized with its specified quotient factorizations. Source: Charts, coefficient
realization (blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartRealizationRestriction {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    chartRestrict φ T ⋙ (sfIntrinsicDerivedEquivalence T A).inverse ≅
      (sfIntrinsicDerivedEquivalence T B).inverse ⋙
        @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) := by
  simpa only [chartRestrict, AlgebraicGeometry.ProEtale.scalarRestriction,
    proEtaleRingRestrictScalars,
    proEtaleCoefficientRestrictScalars, proEtaleConstantRingMap, sfFixedRestriction,
    Sheaf.restrictScalars, Sheaf.derivedRestrictScalars, sfIntrinsicDerivedEquivalence,
    CategoryTheory.Equivalence.mapDerivedCategory, CategoryTheory.Equivalence.mk] using
      Functor.mapDerivedCategorySquareIso (sfInverseRealizationRestriction T φ)

/-- Scalar transport is fixed by the exact restriction square and the normalized
adjunctions. The fixed-site extension is the actual left derived sheaf extension, as
in `chartScalarReassociationMap`. Source: Charts, canonical coefficient comparison
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartRealizationScalarIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T A).functor ⋙ chartScalar φ T ≅
      L(sheafExtendScalars (RingHom.ulift.{u + 1, u + 1, u, u} φ) T) ⋙
        (sfIntrinsicDerivedEquivalence T B).functor := by
  letI := (RingHom.ulift.{u + 1, u + 1, u, u} φ).toAlgebra
  exact (((sfIntrinsicDerivedEquivalence T A).toAdjunction.comp
    (chartScalarAdjunction φ T)).ofNatIsoRight (chartRealizationRestriction φ T)).leftAdjointUniq
        ((leftDerivedSheafExtendScalarsAdjunction
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) T).comp
            (sfIntrinsicDerivedEquivalence T B).toAdjunction)

/-- Chart purity in intrinsic coordinates, with the actual ordered Tate twist and even
shift. Every factor is a specified comparison: ordinary counit-preserving uniqueness,
ordered affine normal form, exact site comparison, and realization unit/counit.
Source: Charts, coordinate-adjunction identification.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartNormalIso (A : Type u) [CommRing A] [Finite A]
    {X Z Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hF : ∀ M : chartCtfCategory X A,
      chartCtf Y A ((chartCompact A j p).obj M.obj))
    (G : chartCtfCategory Y A ⥤ chartCtfCategory X A)
    (adj : chartCtfCompact A j p hF ⊣ G)
    (R : ChartAdjunctionRealization A j p hF G adj)
    (M : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} A))
    (i : U ⟶ X) [IsOpenImmersion i] (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ (j ≫ p) = e ≫ affineTraceProjection Y d)
    (N : ℕ) (hN : 0 < N) (hA : (N : ULift.{u + 1, u} A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} A) N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} A) N hA t T hT)
    (hY : IsUnit (N : Γ(Y, ⊤))) (K : chartCtfCategory Y A) :
    (proEtaleConstantRingDerivedPullback A i).obj (G.obj K).obj ≅
      (sfIntrinsicDerivedEquivalence U A).functor.obj
        ((chartProOperation (ULift.{u + 1, u} A) N hA
          (e ≫ affineTraceProjection Y d) d (2 * (d : ℤ))).obj
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj K.obj)) :=
  chartIntrinsicChartIso A j p hF G adj R M i d e he N hA t D hY K ≪≫
    (chartSite A U).mapIso
      (chartEtaleNormalIso (ULift.{u + 1, u} A) N hN hA Y hY d e (R.origin.obj K)) ≪≫
    (sfIntrinsicDerivedEquivalence U A).functor.mapIso
      ((chartOperationIso (ULift.{u + 1, u} A) N hA
        (e ≫ affineTraceProjection Y d) d (2 * (d : ℤ))).symm.app (R.origin.obj K)) ≪≫
    (sfIntrinsicDerivedEquivalence U A).functor.mapIso
      ((chartProOperation (ULift.{u + 1, u} A) N hA
        (e ≫ affineTraceProjection Y d) d (2 * (d : ℤ))).mapIso
          ((sfIntrinsicDerivedEquivalence Y A).unitIso.app _ ≪≫
            (sfIntrinsicDerivedEquivalence Y A).inverse.mapIso (R.originIso.app K)))





/-- Canonical fixed-coordinate identification of the scalar-extended input.
Source: Charts, scalar realization; the equivalence unit and counit and the normalized
scalar comparison determine this map.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data).
-/
def chartScalarInputIso {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (Y : Scheme.{u}) (K : proEtaleDerivedCategory Y A) :
    L(sheafExtendScalars (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).obj
        ((sfIntrinsicDerivedEquivalence Y A).inverse.obj K) ≅
      (sfIntrinsicDerivedEquivalence Y B).inverse.obj ((chartScalar φ Y).obj K) :=
  (sfIntrinsicDerivedEquivalence Y B).unitIso.app _ ≪≫
    (sfIntrinsicDerivedEquivalence Y B).inverse.mapIso
      ((chartRealizationScalarIso φ Y).symm.app _ ≪≫
        (chartScalar φ Y).mapIso ((sfIntrinsicDerivedEquivalence Y A).counitIso.app K))

/-- The existing scalar reassociation map with its actual source and target, expressed
through the ordinary chart operation. This is the recorded map, including its shift,
tensorator, Tate balancing and pullback factors; it is not chosen from invertibility.
Source: Charts, displayed scalar reassociation.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartReassociation {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {U Y : Scheme.{u}} (g : U ⟶ Y) (d : ℕ)
    (K : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    L(sheafExtendScalars (RingHom.ulift.{u + 1, u + 1, u, u} φ) U).obj
      ((chartProOperation (ULift.{u + 1, u} A) N (congrArg ULift.up hA)
        g d (2 * (d : ℤ))).obj K) ⟶
      (chartProOperation (ULift.{u + 1, u} B) N (congrArg ULift.up hB)
        g d (2 * (d : ℤ))).obj
          (L(sheafExtendScalars (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).obj K) :=
  chartScalarReassociationMap
    (A := ULift.{u + 1, u} A) (B := ULift.{u + 1, u} B)
    (U := U) (Y := Y) (RingHom.ulift.{u + 1, u + 1, u, u} φ) N
    (congrArg ULift.up hA) (congrArg ULift.up hB) g d (2 * (d : ℤ)) K

/-- Realize exactly the recorded scalar reassociation arrow in the intrinsic category.
Source: Charts, canonical pullback/Tate/shift reassociation.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
@[expose] def chartScalarArrow {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {U Y : Scheme.{u}} (g : U ⟶ Y) (d : ℕ) (K : proEtaleDerivedCategory Y A) :
    Arrow (proEtaleDerivedCategory U B) :=
  Arrow.mk ((sfIntrinsicDerivedEquivalence U B).functor.map
    (chartReassociation φ N hA hB g d
      ((sfIntrinsicDerivedEquivalence Y A).inverse.obj K)))



/-- The fixed scalar functor is identified by its actual restriction adjunction.
Source: Stacks 06YY, chart coefficient extension.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartFixedScalarIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    L(sheafExtendScalars φ T) ≅
      CoefficientScalarRepresentatives.extension (ProEt.topology T) φ :=
  letI := φ.toAlgebra
  (leftDerivedSheafExtendScalarsAdjunction A B T).leftAdjointUniq
    (CoefficientScalarRepresentatives.adjunction (ProEt.topology T) φ)

/-- Canonical derived site/scalar comparison for actual ordinary finite coefficients.
The current coefficient-representative comparison is the mate of the exact restriction
square and is computed by ordinary balancing on K-flat representatives.
Source: Stacks 07A4, chart coefficient/site square.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartFixedSiteScalarIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        L(sheafExtendScalars φ T) ≅
      CoefficientScalarRepresentatives.extension T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (chartFixedScalarIso φ T) ≪≫
    CoefficientScalarRepresentatives.comparisonIso T φ

/-- The existing recursively pasted ordinary-etale affine scalar exchange, with the
current restriction-normalized scalar functor in its public type. Its zero case is the
identity. Source: Charts, ordered coordinate exchange.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartOrderedScalarIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (K : Etale.DerivedCategoryModule A S) :
    (CoefficientScalarRepresentatives.extension (affineTraceTower S d).smallEtaleTopology φ).obj
        ((Etale.affineTraceRight A N hA S d).obj K) ≅
      (Etale.affineTraceRight B N hB S d).obj
        ((CoefficientScalarRepresentatives.extension S.smallEtaleTopology φ).obj K) :=
  reductionEtaleAffineScalarIso φ S N hA hB hS d K

/-- The existing single scalar map in ordered right-Tate notation. Its defining
zero-coordinate case is the identity, and positive cases use ordinary Tate balancing.
Source: Charts, ordered scalar normal form.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartOrderedScalarMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (d : ℕ) (K : Etale.DerivedCategoryModule A S) :
    (CoefficientScalarRepresentatives.extension (affineTraceTower S d).smallEtaleTopology φ).obj
        ((Etale.orderedAffineRight A N hA S d).obj K) ⟶
      (Etale.orderedAffineRight B N hB S d).obj
        ((CoefficientScalarRepresentatives.extension S.smallEtaleTopology φ).obj K) :=
  Etale.finiteAffineOrderedScalarMap φ N hA hB S d K

/-- Restrict the actual ordered exchange along the etale coordinate map, using the
canonical scalar/pullback comparison. Source: Charts, chart restriction.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartEtaleScalarIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U S : Scheme.{u}} (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (e : U ⟶ affineTraceTower S d)
    (K : Etale.DerivedCategoryModule A S) :
    (CoefficientScalarRepresentatives.extension U.smallEtaleTopology φ).obj
        ((Etale.ordinaryFinitePullback A e).obj ((Etale.affineTraceRight A N hA S d).obj K)) ≅
      (Etale.ordinaryFinitePullback B e).obj ((Etale.affineTraceRight B N hB S d).obj
        ((CoefficientScalarRepresentatives.extension S.smallEtaleTopology φ).obj K)) :=
  reductionEtaleChartScalarIso φ N hA hB hS d e K

/-- The same single balancing map in left-Tate chart notation.
Source: Charts, displayed single reassociation.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartEtaleReassociation {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {U S : Scheme.{u}} (g : U ⟶ S) (d : ℕ) (K : Etale.DerivedCategoryModule A S) :
    (CoefficientScalarRepresentatives.extension U.smallEtaleTopology φ).obj
        ((chartEtaleOperation A N hA g d (2 * (d : ℤ))).obj K) ⟶
      (chartEtaleOperation B N hB g d (2 * (d : ℤ))).obj
        ((CoefficientScalarRepresentatives.extension S.smallEtaleTopology φ).obj K) :=
  Etale.finiteAffineChartScalarMap φ N hA hB g d (2 * (d : ℤ)) K

/-- The ordered normal form after exact site pullback, before intrinsic realization.
Source: Charts, etale/pro-etale transport of the ordered coordinate identification.
At dimension zero `chartExpandOrderedIso` supplies the pullback, Tate and shift units.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def chartFixedSiteNormalIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) {U : Scheme.{u}}
    (e : U ⟶ affineTraceTower S d) (K : Etale.DerivedCategoryModule A S) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj
        ((Etale.ordinaryFinitePullback A e).obj ((Etale.affineTraceRight A N hA S d).obj K)) ≅
      (chartProOperation A N hA (e ≫ affineTraceProjection S d) d (2 * (d : ℤ))).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj K) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.mapIso
      (chartEtaleNormalIso A N hN hA S hS d e K) ≪≫
    (chartOperationIso A N hA (e ≫ affineTraceProjection S d) d (2 * (d : ℤ))).symm.app K


end AlgebraicGeometry.ProEtale.GeneralFieldChart

namespace AlgebraicGeometry.ProEtale
open GeneralFieldChart

/-- The chart square for the pullback of the exceptional coefficient mate. The two
vertical maps are compositions of the counit-pinned chart normal isomorphisms and the
specified scalar/realization comparisons. They are defined, not existential variables.
Both right endpoints retain the Tate twist `(d)` and shift `[2d]`.
Source: Charts, the last displayed canonical isomorphism.
(blueprint: def-pur-finite-coefficient-chart-adjunction-data). -/
def FiniteCoefficientChartEquation (k : Type u) [Field k]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y U : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsNoetherian U]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hFA : ∀ M : chartCtfCategory X A,
      chartCtf Y A ((chartCompact A j p).obj M.obj))
    (hFB : ∀ M : chartCtfCategory X B,
      chartCtf Y B ((chartCompact B j p).obj M.obj))
    (hSX : ∀ M : chartCtfCategory X A,
      chartCtf X B ((chartScalar φ X).obj M.obj))
    (hSY : ∀ K : chartCtfCategory Y A,
      chartCtf Y B ((chartScalar φ Y).obj K.obj))
    (GA : chartCtfCategory Y A ⥤ chartCtfCategory X A)
    (GB : chartCtfCategory Y B ⥤ chartCtfCategory X B)
    (adjA : chartCtfCompact A j p hFA ⊣ GA)
    (adjB : chartCtfCompact B j p hFB ⊣ GB)
    (RA : ChartAdjunctionRealization A j p hFA GA adjA)
    (RB : ChartAdjunctionRealization B j p hFB GB adjB)
    (MA : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} A))
    (MB : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} B))
    (c : GA ⋙ chartCtfScalar φ X hSX ⟶ chartCtfScalar φ Y hSY ⋙ GB)
    (i : U ⟶ X) [IsOpenImmersion i] (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ (j ≫ p) = e ≫ affineTraceProjection Y d)
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (tA : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} A) N (congrArg ULift.up hA))
    (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} A) N (congrArg ULift.up hA) tA T hT)
    (tB : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} B) N (congrArg ULift.up hB))
    (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} B) N (congrArg ULift.up hB) tB T hT)
    (hY : IsUnit (N : Γ(Y, ⊤))) (K : chartCtfCategory Y A) : Prop :=
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  letI : IsNoetherian X := ⟨⟩
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  letI : IsNoetherian Y := ⟨⟩
  let χA := chartNormalIso A j p hFA GA adjA RA MA i d e he N hN
    (congrArg ULift.up hA) tA DA hY K
  let χB := chartNormalIso B j p hFB GB adjB RB MB i d e he N hN
    (congrArg ULift.up hB) tB DB hY ((chartCtfScalar φ Y hSY).obj K)
  let source := (chartScalarPullbackIso φ i).app (GA.obj K).obj ≪≫
    (chartScalar φ U).mapIso χA ≪≫
    (chartRealizationScalarIso φ U).app _
  let target := χB ≪≫ (sfIntrinsicDerivedEquivalence U B).functor.mapIso
    ((chartProOperation (ULift.{u + 1, u} B) N
      (congrArg ULift.up hB) (e ≫ affineTraceProjection Y d) d (2 * (d : ℤ))).mapIso
        (chartScalarInputIso φ Y K.obj).symm)
  source.hom ≫ (chartScalarArrow φ N hA hB (e ≫ affineTraceProjection Y d) d K.obj).hom =
    (proEtaleConstantRingDerivedPullback B i).map (c.app K).hom ≫ target.hom

end AlgebraicGeometry.ProEtale
