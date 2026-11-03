/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCtfFunctors
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ReductionDirectImageFiniteCoefficients
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfExistence
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.GeoP1Adjunction.GeoP1Adjunction
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteProperLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportSheaves
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import WeilConjectures.CategoryTheory.DerivedInternalHomSectionsModel.DerivedInternalHomSectionsModel
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Algebra.Homology.Ringed.RingedSiteFiniteRetractDualExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenExtensionProducts
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Sf.SfAffineChartFactorizationGluing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantStratifiedZariskiLocality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.OpenDirectImageCtf
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.FiniteCoefficientTensorPullbackEncoding
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.Proper.ProperBoundedConstructible
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorStalk
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricStalkTensorConstantSingle
public import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap
public import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteTorsionEtaleCohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingSubcategoryUniverse
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
public import WeilConjectures.AlgebraicGeometry.NativeAffinePullbackLine.NativeAffinePullbackLineCtf
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import Mathlib.CategoryTheory.Adjunction.Restrict
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Data for finite-coefficient exceptional realization

This is the data-only interface of `det-sp-reduction-exceptional`.  It uses the
current finite pulled-back coefficient rings and the intrinsic pro-etale derived
categories.  The chart record stores the ordered affine-space right adjoint and
its counit; its pro-etale fields are the corresponding transports along the
small-site comparison inverse image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale


/-- The Dctf predicate is equivalent to the bounded, constructible and finite-Tor
conditions used by the finite-coefficient comparison theorem.
Source: det-sp-reduction-direct-image, finite-coefficient comparison clause;
blueprint tag `det-sp-reduction-direct-image`.
Proof: a bounded interval has finite integer support. Conversely finite support
is contained in an interval (use [0,0] if empty). The constructibility and Tor
conditions on the two sides are identical. -/
theorem reductionExceptionalGood (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (M : proEtaleDerivedCategory T A) :
    spFiniteConstructibleTor T A M ↔
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj M)} ∧
        (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
          ((DerivedCategory.homologyFunctor _ i).obj M)) ∧
        HasFiniteProEtaleTorAmplitude T A M := by sorry

local instance reductionExceptionalDiscreteSpace (A : Type u) : TopologicalSpace A := ⊥
local instance reductionExceptionalDiscrete (A : Type u) : DiscreteTopology A := ⟨rfl⟩

/-- Fixed comparison-transfer data on the actual Dctf subcategories for a fixed
compactification. The comparison functors are literally nu^*, P is the recorded
proEtaleLowerShriek, and cf is normalized by the published _hcf formula.
Source: sec-smooth-purity/sk-prop-sp-et-proet/det-sp-et-proet-adjunction-transfer.md,
displayed comparison and counit (blueprint: det-sp-et-proet-adjunction-transfer). -/
structure ReductionExceptionalChartTransfer (R : Type u) [CommRing R] [Finite R]
    {U Y : Scheme.{u}} {g : U ⟶ Y} (c : Compactification g) where
  hX : ∀ K, AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) U K →
    AdjunctionTransfer.proEtaleProperty (ULift.{u + 1} R) U
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) U).mapDerivedCategory.obj K)
  hY : ∀ K, AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) Y K →
    AdjunctionTransfer.proEtaleProperty (ULift.{u + 1} R) Y
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) Y).mapDerivedCategory.obj K)
  eX : (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) U).FullSubcategory ≌
    (AdjunctionTransfer.proEtaleProperty (ULift.{u + 1} R) U).FullSubcategory
  eY : (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) Y).FullSubcategory ≌
    (AdjunctionTransfer.proEtaleProperty (ULift.{u + 1} R) Y).FullSubcategory
  heX : eX.functor = AdjunctionTransfer.comparison (ULift.{u + 1} R) U hX
  heY : eY.functor = AdjunctionTransfer.comparison (ULift.{u + 1} R) Y hY
  hEt : ∀ K, AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) U K →
    AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) Y
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) c).obj K)
  hPro : ∀ K, AdjunctionTransfer.proEtaleProperty (ULift.{u + 1} R) U K →
    AdjunctionTransfer.proEtaleProperty (ULift.{u + 1} R) Y
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) c).obj K)
  cf : AdjunctionTransfer.etaleLowerShriek (ULift.{u + 1} R) c hEt ⋙ eY.functor ≅
    eX.functor ⋙ AdjunctionTransfer.proEtaleLowerShriek (ULift.{u + 1} R) c hPro
  hcf : ∀ K : (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) U).FullSubcategory,
    (cf.inv.app K).hom =
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) c).map
          (eqToHom (congrArg (fun F ↦ (F.obj K).obj) heX)) ≫
      (compactSupportSiteComparison (ULift.{u + 1} R) c).hom.app
        ((AdjunctionTransfer.etaleToPlus (ULift.{u + 1} R) U).obj K) ≫
      eqToHom (congrArg (fun F ↦
        (F.obj ((AdjunctionTransfer.etaleLowerShriek (ULift.{u + 1} R) c hEt).obj K)).obj)
        heY).symm

namespace ReductionExceptionalChartTransfer
variable {R : Type u} [CommRing R] [Finite R] {U Y : Scheme.{u}}
  {g : U ⟶ Y} {c : Compactification g} (T : ReductionExceptionalChartTransfer R c)

/-- The transported right adjoint is the displayed composite, with fixed nu^*.
Source: transfer lemma, displayed G^pro (blueprint: det-sp-et-proet-adjunction-transfer). -/
def right (G : (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) Y).FullSubcategory ⥤
    (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) U).FullSubcategory) :=
  T.eY.inverse ⋙ G ⋙ T.eX.functor

/-- Apply the published transfer construction with its fixed comparison functors
and fixed pro-etale lower shriek. Source: transfer lemma, counit paragraph
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def adjunction
    (G : (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) Y).FullSubcategory ⥤
      (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) U).FullSubcategory)
    (a : AdjunctionTransfer.etaleLowerShriek (ULift.{u + 1} R) c T.hEt ⊣ G) :
    AdjunctionTransfer.proEtaleLowerShriek (ULift.{u + 1} R) c T.hPro ⊣ T.right G :=
  (AdjunctionTransfer.etaleProEtaleAdjunctionTransferOfComparison (ULift.{u + 1} R)
    c T.hX T.hY T.eX T.eY T.heX T.heY T.hEt T.hPro T.cf G a).choose

/-- The actual counit formula, a projection of the recorded transfer theorem.
Source: transfer lemma, displayed counit (blueprint: det-sp-et-proet-adjunction-transfer).
Proof: `adjunction` is the witness chosen from
`etaleProEtaleAdjunctionTransferOfComparison` with exactly these arguments; the
first conjunct of that theorem's specification is this formula for every K. -/
theorem counit_formula
    (G : (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) Y).FullSubcategory ⥤
      (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) U).FullSubcategory)
    (a : AdjunctionTransfer.etaleLowerShriek (ULift.{u + 1} R) c T.hEt ⊣ G)
    (K : (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) Y).FullSubcategory) :
    (T.adjunction G a).counit.app (T.eY.functor.obj K) =
      (AdjunctionTransfer.proEtaleLowerShriek (ULift.{u + 1} R) c T.hPro).map
        (T.eX.functor.map (G.map (T.eY.unitIso.inv.app K))) ≫
        T.cf.inv.app (G.obj K) ≫ T.eY.functor.map (a.counit.app K) := by
  sorry
end ReductionExceptionalChartTransfer

/-- Coordinate-chart data. Ordinary right adjoints and adjunctions below are
computed from sum/evaluation followed by affineTraceAdjunction; their Dctf
restrictions and pro-etale transports are definitions, not fields.
Source: sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md,
Charts step (blueprint: det-sp-reduction-exceptional). -/
structure ReductionExceptionalChartCounit (R : Type u) [CommRing R] [Finite R]
    {X Y U : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) (u : U ⟶ X)
    [IsOpenImmersion u] (e : U ⟶ affineTraceTower Y d)
    (hu : u ≫ f = e ≫ affineTraceProjection Y d)
    (N : ℕ) (hN : (N : ULift.{u + 1} R) = 0)
    [AlgebraicGeometry.Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] where
  t : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1} R) N hN
  D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
    Etale.OrdinaryFiniteP1Datum (ULift.{u + 1} R) N hN t T hT
  normalization : Etale.EtaleCompactSupportNormalization (ULift.{u + 1} R)
  c : Compactification (e ≫ affineTraceProjection Y d)
  transfer : ReductionExceptionalChartTransfer R c
  hG : ∀ K : (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) Y).FullSubcategory,
    AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) U
      ((Etale.affineTraceRight (ULift.{u + 1} R) N hN Y d ⋙
        Etale.ordinaryFinitePullback (ULift.{u + 1} R) e).obj K.obj)

/-- The fixed-scalar pro-etale Dctf presentation maps to the intrinsic Dctf
presentation by the existing coefficient realization.
Source: det-sp-reduction-exceptional, coefficient realization in Existence
(blueprint: det-sp-reduction-exceptional).
Proof: the exact coefficient equivalence preserves homology and derived tensor.
The bounded etale-origin constructibility condition is equivalent to intrinsic
finite constructibility, and the Tor intervals are unchanged. -/
theorem reductionExceptionalNativeMembership (R : Type u) [CommRing R] [Finite R]
    (T : Scheme.{u})
    (K : (AdjunctionTransfer.proEtaleProperty (ULift.{u + 1} R) T).FullSubcategory) :
    spFiniteConstructibleTor T R ((sfIntrinsicDerivedEquivalence T R).functor.obj K.obj) :=
  by sorry

/-- The actual restricted intrinsic coefficient realization, with fixed forward
functor. Source: Existence step (blueprint: det-sp-reduction-exceptional). -/
def reductionExceptionalNativeFunctor (R : Type u) [CommRing R] [Finite R]
    (T : Scheme.{u}) :=
  (spFiniteConstructibleTor T R).lift
    ((AdjunctionTransfer.proEtaleProperty (ULift.{u + 1} R) T).ι ⋙
      (sfIntrinsicDerivedEquivalence T R).functor)
    (reductionExceptionalNativeMembership R T)

/-- The fixed intrinsic coefficient realization restricts to an equivalence on
Dctf. Source: Existence step (blueprint: det-sp-reduction-exceptional).
Proof: the ambient equivalence is fully faithful. Its inverse preserves the
same constructibility, boundedness and Tor conditions, so every intrinsic Dctf
object has a preimage in the fixed-scalar Dctf category. -/
theorem reductionExceptionalNativeFunctor_isEquivalence
    (R : Type u) [CommRing R] [Finite R] (T : Scheme.{u}) :
    (reductionExceptionalNativeFunctor R T).IsEquivalence := by sorry

/-- The single fixed change from fixed-scalar to intrinsic pro-etale Dctf
coordinates. Source: Existence step (blueprint: det-sp-reduction-exceptional). -/
def reductionExceptionalNativeEquivalence (R : Type u) [CommRing R] [Finite R]
    (T : Scheme.{u}) :=
  letI := reductionExceptionalNativeFunctor_isEquivalence R T
  (reductionExceptionalNativeFunctor R T).asEquivalence

namespace ReductionExceptionalChartCounit
variable {R : Type u} [CommRing R] [Finite R] {X Y U : Scheme.{u}}
  {f : X ⟶ Y} {d : ℕ} {u : U ⟶ X} [IsOpenImmersion u]
  {e : U ⟶ affineTraceTower Y d} [AlgebraicGeometry.Etale e] [IsSeparated e]
  [LocallyOfFiniteType e] [QuasiCompact e]
  {hu : u ≫ f = e ≫ affineTraceProjection Y d}
  {N : ℕ} {hN : (N : ULift.{u + 1} R) = 0}
  (C : ReductionExceptionalChartCounit R f d u e hu N hN)

/-- The finite pro-etale Tate line is literally nu^* of the finite etale line.
Source: Charts step, Tate convention (blueprint: det-sp-reduction-exceptional). -/
def proEtaleTateLine :=
  let _ := C
  CondensedRing.finiteShriekProEtaleTateLine U R N hN 1

/-- The ordinary chart right functor e^*p_d^*(-)(d)[2d], in the ordered trace
model. Source: Charts step (blueprint: det-sp-reduction-exceptional). -/
def ordinaryRight :=
  let _ := C
  Etale.affineTraceRight (ULift.{u + 1} R) N hN Y d ⋙
  Etale.ordinaryFinitePullback (ULift.{u + 1} R) e

/-- The displayed pullback, finite Tate twist and [2d] shift, followed by e^*.
Source: Charts step, G_d,R (blueprint: det-sp-reduction-exceptional). -/
def ordinaryTwistedPullback :=
  let _ := C
  (Etale.ordinaryFinitePullback (ULift.{u + 1} R) (affineTraceProjection Y d) ⋙
    Etale.derivedTensorRight (ModuleCat.{u + 1} (ULift.{u + 1} R)) (affineTraceTower Y d)
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf (ULift.{u + 1} R) N
          (affineTraceTower Y d) hN (d : ℤ))) ⋙ shiftFunctor _ (2 * (d : ℤ))) ⋙
    Etale.ordinaryFinitePullback (ULift.{u + 1} R) e

/-- The ordered affine model has exactly the finite Tate-twisted shifted
pullback normal form. Source: Charts step and affine-space top trace
(blueprint: det-sp-reduction-exceptional).
Proof: `affineTraceRight_normalForm` gives an isomorphism from the ordered affine
right functor to pullback along p_d, tensor with the finite Tate sheaf and shift
by 2d. Whisker it on the right with the etale pullback along e. -/
theorem ordinaryRight_normalForm [IsNoetherian Y] (hpos : 0 < N)
    (hY : IsUnit (N : Γ(Y, ⊤))) : Nonempty (C.ordinaryRight ≅ C.ordinaryTwistedPullback) := by
  sorry

/-- The actual sum/evaluation followed by affine-trace adjunction.
Source: Charts step, first paragraph (blueprint: det-sp-reduction-exceptional). -/
def ordinaryAdjunction [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) :=
  reductionEtaleChartAdjunction (ULift.{u + 1} R) Y N hN C.t C.D hY d e

/-- The ordinary adjunction is canonical by construction.
Source: Charts step (blueprint: det-sp-reduction-exceptional).
Proof: unfold `ordinaryAdjunction`; both sides are the same term. -/
theorem ordinaryAdjunction_canonical [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) :
    C.ordinaryAdjunction hY =
      reductionEtaleChartAdjunction (ULift.{u + 1} R) Y N hN C.t C.D hY d e := by
  sorry

/-- On the constant input the chart counit is exactly etale sum/evaluation
followed by the named ordered affine trace, in that order.
Source: Charts step, counit normalization (blueprint: det-sp-reduction-exceptional).
Proof: `ordinaryAdjunction` is the composite of the derived sum/evaluation
adjunction of e with `affineTraceAdjunction`. The counit of a composite adjunction
at an object is the outer left functor applied to the inner counit, followed by
the outer counit (`Adjunction.comp_counit_app`); the outer counit is
`affineTraceCounit`. -/
theorem ordinaryCounit_unit [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) :
    (C.ordinaryAdjunction hY).counit.app (Etale.ordinaryFiniteUnit (ULift.{u + 1} R) Y) =
      (Etale.affineTraceLeft (ULift.{u + 1} R) Y d).map
        (((Etale.derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} R)) e inferInstance).ofNatIsoRight
            (Etale.leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} (ULift.{u + 1} R)) e).symm).counit.app
          ((Etale.affineTraceRight (ULift.{u + 1} R) N hN Y d).obj
            (Etale.ordinaryFiniteUnit (ULift.{u + 1} R) Y))) ≫
        Etale.affineTraceCounit (ULift.{u + 1} R) N hN C.t C.D Y hY d := by
  sorry

/-- Restrict the ordered chart right functor to the recorded etale Dctf property.
Source: Charts step, G_d,R (blueprint: det-sp-reduction-exceptional). -/
def ordinaryRightSmall := (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) U).lift
  ((AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) Y).ι ⋙ C.ordinaryRight) C.hG

/-- Canonical chart left comparison: etale sum extension, ordered affine
compactification, then the graph-normalized composition comparison.
Source: Charts step (blueprint: det-sp-reduction-exceptional). -/
def ordinaryLeftIso [IsNoetherian Y] [IsNoetherian U] :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} R)) e
      inferInstance).mapDerivedCategory ⋙ Etale.affineTraceLeft (ULift.{u + 1} R) Y d ≅
    Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} R)) C.c := by
  letI := affineTraceNoetherian Y d
  let cp := HasCompactification.compactification (affineTraceProjection Y d)
  exact Functor.isoWhiskerLeft _ (reductionEtaleAffineLeftIso (ULift.{u + 1} R) Y d cp) ≪≫
    Etale.etaleAmbientLeftComparison (ULift.{u + 1} R) C.normalization
      e (affineTraceProjection Y d) cp C.c

/-- Restrict the actual chart adjunction, after the canonical left comparison.
Source: Charts and transfer steps (blueprint: det-sp-reduction-exceptional). -/
def ordinarySmallAdjunction [IsNoetherian Y] [IsNoetherian U]
    (hY : IsUnit (N : Γ(Y, ⊤))) :
    AdjunctionTransfer.etaleLowerShriek (ULift.{u + 1} R) C.c C.transfer.hEt ⊣
      C.ordinaryRightSmall :=
  ((C.ordinaryAdjunction hY).ofNatIsoLeft C.ordinaryLeftIso).restrictFullyFaithful
    (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) U).fullyFaithfulι
    (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) Y).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- G_d,R on pro-etale Dctf is the required nu^*-transport of the etale
ordered Tate-twisted shifted pullback.
Source: Charts/transfer step (blueprint: det-sp-reduction-exceptional). -/
def proEtaleRight := C.transfer.right C.ordinaryRightSmall

/-- The chart pro-etale adjunction is the published comparison transfer.
Source: Charts/transfer step (blueprint: det-sp-reduction-exceptional). -/
def proEtaleAdjunction [IsNoetherian Y] [IsNoetherian U] (hY : IsUnit (N : Γ(Y, ⊤))) :=
  C.transfer.adjunction C.ordinaryRightSmall (C.ordinarySmallAdjunction hY)

/-- The actual chart counit epsilon_d,R, not an independently supplied arrow.
Source: Charts step, counit formula (blueprint: det-sp-reduction-exceptional). -/
def proEtaleCounit [IsNoetherian Y] [IsNoetherian U] (hY : IsUnit (N : Γ(Y, ⊤))) :=
  (C.proEtaleAdjunction hY).counit

/-- The normalized transfer counit formula for this chart and its canonical
ordinary adjunction. Source: Charts/transfer step
(blueprint: det-sp-reduction-exceptional).
Proof: `proEtaleCounit` is the counit of `transfer.adjunction` applied to the
restricted ordinary adjunction; apply `ReductionExceptionalChartTransfer.counit_formula`
with G the restricted ordinary right functor. -/
theorem proEtaleCounit_formula [IsNoetherian Y] [IsNoetherian U]
    (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : (AdjunctionTransfer.etaleProperty (ULift.{u + 1} R) Y).FullSubcategory) :
    (C.proEtaleCounit hY).app (C.transfer.eY.functor.obj K) =
      (AdjunctionTransfer.proEtaleLowerShriek (ULift.{u + 1} R) C.c C.transfer.hPro).map
        (C.transfer.eX.functor.map
          (C.ordinaryRightSmall.map (C.transfer.eY.unitIso.inv.app K))) ≫
        C.transfer.cf.inv.app (C.ordinaryRightSmall.obj K) ≫
        C.transfer.eY.functor.map ((C.ordinarySmallAdjunction hY).counit.app K) := by
  sorry

/-- G_d,R in the intrinsic pro-etale Dctf categories used by the item.
Source: Charts step, comparison transport (blueprint: det-sp-reduction-exceptional). -/
def right := (reductionExceptionalNativeEquivalence R Y).inverse ⋙
  C.proEtaleRight ⋙ (reductionExceptionalNativeEquivalence R U).functor

/-- Compact support on a chart preserves intrinsic Dctf.
Source: Charts/transfer step and finite compact-support preservation
(blueprint: det-sp-reduction-exceptional).
Proof: move an intrinsic Dctf object through the fixed coefficient equivalence.
The fixed-scalar compact-support functor preserves proEtaleProperty by hPro.
Use reductionCompactSupportFixedIso to return its value to the intrinsic
compact-support composite for the identical compactification. -/
theorem compactSupportPreserves :
    ∀ M : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R C.c.i C.c.g).obj M.obj) :=
  by sorry

/-- The chart's actual intrinsic compact-support functor for its given
compactification. Source: Charts step (blueprint: det-sp-reduction-exceptional). -/
def left := reductionCtfCompactSupport R C.c.i C.c.g C.compactSupportPreserves

/-- The canonical comparison from the transported compact-support functor to
that actual intrinsic functor, using the fixed open/proper realization comparison.
Source: Charts/transfer step (blueprint: det-sp-reduction-exceptional). -/
def leftIso :
    (reductionExceptionalNativeEquivalence R U).inverse ⋙
      AdjunctionTransfer.proEtaleLowerShriek (ULift.{u + 1} R) C.c C.transfer.hPro ⋙
        (reductionExceptionalNativeEquivalence R Y).functor ≅ C.left := by
  let eU := reductionExceptionalNativeEquivalence R U
  let eY := reductionExceptionalNativeEquivalence R Y
  let t : eU.functor ⋙ C.left ≅
      AdjunctionTransfer.proEtaleLowerShriek (ULift.{u + 1} R) C.c C.transfer.hPro ⋙
        eY.functor :=
    ((spFiniteConstructibleTor Y R).fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft
        (AdjunctionTransfer.proEtaleProperty (ULift.{u + 1} R) U).ι
        (reductionCompactSupportFixedIso R C.c.i C.c.g))
  exact Functor.isoWhiskerLeft eU.inverse t.symm ≪≫ eU.invFunIdAssoc C.left

/-- The chart adjunction for the actual intrinsic compact-support functor.
Its counit uses the canonical realization comparison, not an unspecified map.
Source: Charts/transfer step (blueprint: det-sp-reduction-exceptional). -/
def adjunction [IsNoetherian Y] [IsNoetherian U] (hY : IsUnit (N : Γ(Y, ⊤))) :
    C.left ⊣ C.right :=
  (((reductionExceptionalNativeEquivalence R U).symm.toAdjunction.comp
    (C.proEtaleAdjunction hY)).comp
      (reductionExceptionalNativeEquivalence R Y).toAdjunction).ofNatIsoLeft C.leftIso

/-- The actual intrinsic pro-etale Tate line is the realization of nu^*R_U(1).
Source: Charts step, Tate convention (blueprint: det-sp-reduction-exceptional). -/
def tateLine := (sfIntrinsicModuleEquivalence U R).functor.obj C.proEtaleTateLine

/-- Epsilon_d,R in the intrinsic categories is the transported chart counit.
Source: Charts step, displayed counit (blueprint: det-sp-reduction-exceptional). -/
def counit [IsNoetherian Y] [IsNoetherian U] (hY : IsUnit (N : Γ(Y, ⊤))) :=
  (C.adjunction hY).counit

end ReductionExceptionalChartCounit

/-- Finite-type schemes over a field are Noetherian.
Source: det-sp-reduction-exceptional, standing setting for Charts
(blueprint: det-sp-reduction-exceptional).
Proof: Spec k is Noetherian, finite type gives local Noetherianity, and
quasi-compactness makes the scheme Noetherian. -/
theorem reductionExceptionalNoetherian (k : Type u) [Field k]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] :
    IsNoetherian T := by sorry

/-- An open subscheme of a Noetherian scheme is Noetherian.
Source: det-sp-reduction-exceptional, coordinate-chart setting
(blueprint: det-sp-reduction-exceptional).
Proof: local Noetherianity restricts to opens, and every open of a Noetherian
space is quasi-compact. Apply this to the open immersion's image. -/
theorem reductionExceptionalOpenNoetherian {T V : Scheme.{u}}
    [IsNoetherian T] (v : V ⟶ T) [IsOpenImmersion v] : IsNoetherian V := by sorry

/-- The actual chart trace exponent is invertible in the standing setting.
Source: det-sp-reduction-exceptional, Charts, finite Tate convention
(blueprint: det-sp-reduction-exceptional).
Proof: ell is prime and distinct from the field characteristic, so its image
in k is a nonzero unit. Its nth power stays a unit; map this unit along the
the structure morphism to global sections of T. -/
theorem reductionExceptionalExponentUnit (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (hchar : ringChar k ≠ ell)
    (T : Scheme.{u}) [T.Over (Spec (.of k))] (n : ℕ) :
    IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤)) := by sorry

/-- The fixed finite-coefficient scalar and exceptional data used by the reduction
exceptional construction.  The comparison `b` is the compact-support coefficient
isomorphism.  The morphism `c` is equipped with its defining counit-transpose
identity; therefore it is not supplied by an unconstrained existence proposition.
Chart counits are the transported ordered affine-space counits, with the finite
etale Tate line and the affine trace normalization.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.md, Existence and Charts data
(blueprint: def-sp-reduction-exceptional-realization-objects), a data sub-step of
(blueprint: det-sp-reduction-exceptional). -/
structure ReductionExceptionalRealizationObjects
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ℓ)
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))]
    (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (n : ℕ)
    (hAn : ∀ x : A, ((ℓ ^ n : ℕ) : A) • x = 0)
    (hBn : ∀ x : B, ((ℓ ^ n : ℕ) : B) • x = 0)
    (φ : A →+* B) where
  hFA : ∀ M : spFiniteConstructibleTorCategory X A,
    spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj)
  hFB : ∀ M : spFiniteConstructibleTorCategory X B,
    spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj)
  hSX : ∀ M : spFiniteConstructibleTorCategory X A,
    spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj)
  hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
    spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj)
  c :
    let suppliedA := ReductionExceptionalSuppliedAdjunction ℓ k hk hchar f A
      ⟨n, by simpa using hAn 1⟩ j p hf hFA
    let suppliedB := ReductionExceptionalSuppliedAdjunction ℓ k hk hchar f B
      ⟨n, by simpa using hBn 1⟩ j p hf hFB
    suppliedA.1 ⋙ reductionCtfScalar φ X hSX ⟶
      reductionCtfScalar φ Y hSY ⋙ suppliedB.1
  c_counit :
    let suppliedA := ReductionExceptionalSuppliedAdjunction ℓ k hk hchar f A
      ⟨n, by simpa using hAn 1⟩ j p hf hFA
    let suppliedB := ReductionExceptionalSuppliedAdjunction ℓ k hk hchar f B
      ⟨n, by simpa using hBn 1⟩ j p hf hFB
    ∀ K : spFiniteConstructibleTorCategory Y A,
    (reductionCompactSupport B j p).map (c.app K).hom ≫
        (suppliedB.2.counit.app
          ((reductionCtfScalar φ Y hSY).obj K)).hom =
      @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app
        (suppliedA.1.obj K).obj)
        (by
          have hgood :=
            (reductionExceptionalGood X A (suppliedA.1.obj K).obj).mp
              (suppliedA.1.obj K).property
          exact
            (reductionDirectImage_finiteCoefficients_isIso ℓ k hk hchar f j p hf
              ⟨n, by simpa [nsmul_eq_mul] using hAn⟩
              ⟨n, by simpa [nsmul_eq_mul] using hBn⟩ φ
              (suppliedA.1.obj K).obj
              hgood.1 hgood.2.1 hgood.2.2).1) ≫
        (scalarExtensionFunctor φ Y).map (suppliedA.2.counit.app K).hom
  chartA : ∀ {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (hu : u ≫ f = e ≫ affineTraceProjection Y d),
    ReductionExceptionalChartCounit A f d u e hu (ℓ ^ n) (by
      apply ULift.ext
      simpa using hAn 1)
  chartB : ∀ {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (hu : u ≫ f = e ≫ affineTraceProjection Y d),
    ReductionExceptionalChartCounit B f d u e hu (ℓ ^ n) (by
      apply ULift.ext
      simpa using hBn 1)

namespace ReductionExceptionalRealizationObjects
variable
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ℓ)
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))]
    (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (n : ℕ)
    (hAn : ∀ x : A, ((ℓ ^ n : ℕ) : A) • x = 0)
    (hBn : ∀ x : B, ((ℓ ^ n : ℕ) : B) • x = 0)
    (φ : A →+* B)
    (D : ReductionExceptionalRealizationObjects ℓ k hk hchar f d j p hf n hAn hBn φ)

/-- The A chart counit in the actual geometric setting, with Noetherianity and
invertibility derived from that setting rather than assumed as record fields.
Source: Charts step (blueprint: det-sp-reduction-exceptional). -/
def chartACounit {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (hu : u ≫ f = e ≫ affineTraceProjection Y d) :=
  letI := reductionExceptionalNoetherian k X
  letI := reductionExceptionalNoetherian k Y
  letI := reductionExceptionalOpenNoetherian u
  (D.chartA u e hu).counit (reductionExceptionalExponentUnit ℓ k hchar Y n)

/-- The B chart counit in the same setting and with the same trace exponent.
Source: Charts step (blueprint: det-sp-reduction-exceptional). -/
def chartBCounit {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (hu : u ≫ f = e ≫ affineTraceProjection Y d) :=
  letI := reductionExceptionalNoetherian k X
  letI := reductionExceptionalNoetherian k Y
  letI := reductionExceptionalOpenNoetherian u
  (D.chartB u e hu).counit (reductionExceptionalExponentUnit ℓ k hchar Y n)

end ReductionExceptionalRealizationObjects

end AlgebraicGeometry.ProEtale
