/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteClosedExceptional
public import WeilConjectures.SixFunctors.ZeroSectionSupportedCohomology
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1Decomposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicSectionCoordinates
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.DerivedDegreeZeroNormalization
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.RingedTensorEdge.RingedTensorEdgeInducedAdjunction
import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.Sheaf.SheafSliceOrdinaryData
import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafSliceAdjunction
import WeilConjectures.CategoryTheory.Ringed.RingedPresentationData
import WeilConjectures.CategoryTheory.RingedCoefficientCounit.RingedCoefficientCounitPresentations
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.ProperBaseChange.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.ProperBaseChange.ContinuousCocontinuousRingedRestriction
import WeilConjectures.CategoryTheory.ProperBaseChange.ElementSiteDescent
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Ringed.RingedSliceDerivedComparisons
import WeilConjectures.Algebra.Homology.Ringed.RingedSliceDerivedMate
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.ProperBaseChange.ElementRestrictionHom
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# The Brown exceptional orientation of the affine-line zero section

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/det-prop-a1.md
and det-prop-a1.proof.md (blueprint: det-prop-a1).
The general-field closed-case extension uses the recorded condensed Brown construction.
Its canonical adjunction comparison recovers the literal recorded operation, and a
separate corollary states the result on that operation. The comparison with ordinary
etale coefficients is fixed by compact-support counits.
The boundary is the published supported-localization boundary applied to the actual
Kummer connecting class. Supported cohomology is the recorded pur9 definition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilConjectures.AffineLineOrientation

section FiniteCoordinates

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

/-- Exact etale comparison, in fixed scalar coordinates.
Source: Step 1, finite comparison (blueprint: det-prop-a1). -/
abbrev nu (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory

/-- The same etale complex in the normalized native condensed coordinates.
Source: Step 1, finite comparison (blueprint: det-prop-a1). -/
def native (T : Scheme.{u})
    (K : DerivedCategory (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  (encoding A T).fixedDerived.inverse.obj ((nu A T).obj K)

/-- The counit of the normalized encoding, with its literal etale source retained.
Source: Step 1, finite comparison (blueprint: det-prop-a1). -/
def nativeIso (T : Scheme.{u})
    (K : DerivedCategory (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (encoding A T).fixedDerived.functor.obj (native A T K) ≅ (nu A T).obj K :=
  (encoding A T).fixedDerived.counitIso.app _

/-- Canonical direct-image comparison, the identity on additive sections.
Source: the compactification comparison chi in Step 1 (blueprint: det-prop-a1). -/
def pushEncoding {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor ⋙
        (encoding A Y).fixedDerived.functor ≅
      (encoding A X).fixedDerived.functor ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor := by
  letI : ((encoding A Y).ordinary.trans (encoding A Y).fixed).functor.Additive :=
    inferInstanceAs ((encoding A Y).ordinary.functor ⋙ (encoding A Y).fixed.functor).Additive
  letI : ((encoding A X).ordinary.trans (encoding A X).fixed).functor.Additive :=
    inferInstanceAs ((encoding A X).ordinary.functor ⋙ (encoding A X).fixed.functor).Additive
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (encodingPushforwardNatIso A Y X f (encoding A Y) (encoding A X)) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso _ _

/-- The open comparison is the unique comparison of the two left adjoints to the
same normalized restriction. Source: chi, Step 1 (blueprint: det-prop-a1). -/
def openEncoding {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    CondensedRing.openImmersionLowerShriek (coefficient A) j ⋙
        ((encoding A Y).ordinary.trans (encoding A Y).fixed).functor ≅
      ((encoding A X).ordinary.trans (encoding A X).fixed).functor ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j := by
  let EX := (encoding A X).ordinary.trans (encoding A X).fixed
  let EY := (encoding A Y).ordinary.trans (encoding A Y).fixed
  let i := encodingPushforwardNatIso A Y X j (encoding A Y) (encoding A X)
  let k := Iso.isoCompInverse (H := EY) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EX) k
  let pull := ((EY.toAdjunction.comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)).leftAdjointUniq
      (((CondensedRing.upperStarLowerStarAdjunction (coefficient A) j).comp
        EX.toAdjunction).ofNatIsoRight kr)).symm
  let kr' := Iso.inverseCompIso (G := EY)
    (Iso.isoCompInverse (H := EX) pull ≪≫ Functor.associator _ _ _)
  exact ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction (coefficient A) j).comp
    EY.toAdjunction).leftAdjointUniq
      ((EX.toAdjunction.comp (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)).ofNatIsoRight kr'.symm)

/-- The actual proper/open comparison chi, computed on the retained compactification.
Source: Step 1 and lem-sf-condensed-finite-exceptional-comparison
(blueprint: det-prop-a1). -/
def compactSupportEncoding {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c ⋙
        (encoding A Y).fixedDerived.functor ≅
      (encoding A X).fixedDerived.functor ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c := by
  letI : ((encoding A X).ordinary.trans (encoding A X).fixed).functor.Additive :=
    inferInstanceAs ((encoding A X).ordinary.functor ⋙ (encoding A X).fixed.functor).Additive
  letI : ((encoding A Y).ordinary.trans (encoding A Y).fixed).functor.Additive :=
    inferInstanceAs ((encoding A Y).ordinary.functor ⋙ (encoding A Y).fixed.functor).Additive
  letI : ((encoding A c.Z).ordinary.trans (encoding A c.Z).fixed).functor.Additive :=
    inferInstanceAs
      ((encoding A c.Z).ordinary.functor ⋙ (encoding A c.Z).fixed.functor).Additive
  let o := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openEncoding A c.i) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pushEncoding A c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight o _ ≪≫ Functor.associator _ _ _

/-- The root line in degree zero; the exponent is an actual annihilator of A.
Source: det-def-purity-conv, finite twist (blueprint: det-prop-a1). -/
abbrev root (N : ℕ) (hA : (N : ULift.{u + 1} A) = 0) (T : Scheme.{u}) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateLine T N (ULift.{u + 1} A) hA)

/-- The free-coefficient comparison used to lift the actual abelian Kummer class.
Source: det-def-purity-conv, Kummer connecting map (blueprint: det-prop-a1).
Proof: maps out of the constant free rank-one module are global sections, by
sending a linear map to its value at one. Scalar forgetting preserves injectives
for this calculation since its left adjoint is exact free extension. Apply that
comparison to an injective resolution; the induced map is ordinaryFiniteClass. -/
theorem classToAbelian_bijective (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    Function.Bijective (Etale.ordinaryFiniteClass (ULift.{u + 1} A) T F 1) := by
  sorry

/-- The genuine Kummer boundary of a unit, extended by z to 1 tensor z.
Its lift is through a specified bijection, so no generator is selected arbitrarily.
Source: det-def-purity-conv, kappa(t) (blueprint: det-prop-a1). -/
def kummer (N : ℕ) (hA : (N : ULift.{u + 1} A) = 0) (T : Scheme.{u})
    (hr : IsUnit (N : Γ(T, ⊤))) (v : Γ(T, ⊤)ˣ) :
    Etale.constantComplex (ULift.{u + 1} A) T ⟶ (root A N hA T)⟦(1 : ℤ)⟧ :=
  (Equiv.ofBijective _ (classToAbelian_bijective A T
    (Scheme.finiteEtaleTateLine T N (ULift.{u + 1} A) hA))).symm
      (Sheaf.H.map (Etale.ordinaryFiniteRootMap (ULift.{u + 1} A) N hA T) 1
        (T.kummerδ₀ N hr (Additive.ofMul v)))

/-- Pullback of the root line, normalized on roots and pure tensors.
Source: det-def-purity-conv, base change (blueprint: det-prop-a1). -/
def rootPullback (N : ℕ) (hN : 0 < N) (hA : (N : ULift.{u + 1} A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hr : IsUnit (N : Γ(Y, ⊤))) :
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor.obj
        (root A N hA Y) ≅ root A N hA X :=
  (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
      f).leftDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
      f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Etale.p1DecompositionSheafPullback (ULift.{u + 1} A) N hN hA f hr 1)

/-- The closed-open range equality for the actual zero section and D(t).
Source: Step 1, localization (blueprint: det-prop-a1).
Proof: the common zero locus of the single coordinate is the zero section. -/
theorem complement (Y : Scheme.{u}) :
    Set.range (PurityFiniteSetting.zeroSection Y).base =
      (Set.range (PurityFiniteSetting.openImmersion Y).base)ᶜ := by
  sorry

/-- The recorded geometric zero section is closed. Source: Step 1
(blueprint: det-prop-a1). -/
instance zeroSectionClosed (Y : Scheme.{u}) :
    IsClosedImmersion (PurityFiniteSetting.zeroSection Y) :=
  inferInstanceAs (IsClosedImmersion (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y))

/-- Use the identity/proper compactification for the ordinary etale adjoint.
Source: Step 1 (blueprint: det-prop-a1). -/
instance zeroSectionCompactification (Y : Scheme.{u}) :
    HasCompactification (PurityFiniteSetting.zeroSection Y) :=
  ⟨⟨Compactification.ofIsProper (PurityFiniteSetting.zeroSection Y)⟩⟩

/-- The supported localization boundary applied to the concrete coordinate Kummer class.
All shifts have the sign convention of supportedLocalizationBoundary.
Source: Steps 1 and 3, delta kappa(t) (blueprint: det-prop-a1). -/
def etaleBoundary (N : ℕ) (hN : 0 < N) (hA : (N : ULift.{u + 1} A) = 0)
    (Y : Scheme.{u}) (hr : IsUnit (N : Γ(PurityFiniteSetting.Line Y, ⊤))) :
    Etale.constantComplex (ULift.{u + 1} A) (PurityFiniteSetting.Line Y) ⟶
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A))
        (PurityFiniteSetting.zeroSection Y)).obj
          ((Etale.rightDerivedUpperShriek (ULift.{u + 1} A)
            (PurityFiniteSetting.zeroSection Y)).obj
              (root A N hA (PurityFiniteSetting.Line Y))))⟦(2 : ℤ)⟧ :=
  let j := PurityFiniteSetting.openImmersion Y
  let i := PurityFiniteSetting.zeroSection Y
  let L := root A N hA (PurityFiniteSetting.Line Y)
  letI : IsClosedImmersion i := zeroSectionClosed Y
  letI : IsOpenImmersion j :=
    inferInstanceAs (IsOpenImmersion ((PurityFiniteSetting.Line Y).basicOpen
      (PurityFiniteSetting.coordinate Y)).ι)
  let r : IsUnit (N : Γ(PurityFiniteSetting.Punctured Y, ⊤)) := by
    simpa using hr.map j.appTop.hom
  ((Etale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).homEquiv _ _
    ((Etale.leftDerivedUpperStarConstantComplexIso (ULift.{u + 1} A) j).hom ≫
      kummer A N hA _ r (PurityFiniteSetting.coordinateUnit Y) ≫
        (rootPullback A N hN hA j hr).inv⟦(1 : ℤ)⟧')) ≫
    ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
      j).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app _ ≫
    (Etale.supportedLocalizationBoundary (ULift.{u + 1} A) i j (complement Y) L)⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd' _ (1 : ℤ) 1 2 rfl).inv.app _

/-- The closed exceptional value is bounded below, also after the orientation shift.
Source: Step 1, closed support, and Step 4 (blueprint: det-prop-a1).
Proof: closed direct image is exact. Its ordinary support right adjoint is left exact,
so its total right derived functor preserves bounded-below objects. The input is a
single sheaf, and a fixed shift preserves bounded-below objects. -/
theorem etaleValuePlus (N : ℕ) (hA : (N : ULift.{u + 1} A) = 0) (Y : Scheme.{u})
    (q : ℤ) : DerivedCategory.TStructure.t.plus
      (((Etale.rightDerivedUpperShriek (ULift.{u + 1} A)
        (PurityFiniteSetting.zeroSection Y)).obj
          (root A N hA (PurityFiniteSetting.Line Y)))⟦q⟧) := by
  sorry

/-- The finite exceptional object in ordinary etale coordinates.
Source: Step 1, theta comparison (blueprint: det-prop-a1). -/
abbrev etaleValue (N : ℕ) (hA : (N : ULift.{u + 1} A) = 0) (Y : Scheme.{u}) :=
  (Etale.rightDerivedUpperShriek (ULift.{u + 1} A)
    (PurityFiniteSetting.zeroSection Y)).obj (root A N hA (PurityFiniteSetting.Line Y))

/-- Remove the zero shift in the bounded-below assertion.
Source: Step 1 (blueprint: det-prop-a1).
Proof: transport etaleValuePlus at zero along the canonical zero-shift isomorphism. -/
theorem etaleValueUnshiftedPlus (N : ℕ) (hA : (N : ULift.{u + 1} A) = 0)
    (Y : Scheme.{u}) : DerivedCategory.TStructure.t.plus (etaleValue A N hA Y) := by
  sorry

/-- Its unshifted transported counit, formed from chi, exact site comparison, and the
ordinary etale counit. This fixes theta and rules out rescaling it by a unit.
Source: Step 1, displayed counit compatibility in
lem-sf-condensed-finite-exceptional-comparison (blueprint: det-prop-a1). -/
def transportedCounit (N : ℕ) (hA : (N : ULift.{u + 1} A) = 0) (Y : Scheme.{u})
    (c : Compactification (PurityFiniteSetting.zeroSection Y)) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c).obj
        (native A Y (etaleValue A N hA Y)) ⟶
      native A (PurityFiniteSetting.Line Y) (root A N hA (PurityFiniteSetting.Line Y)) :=
  (encoding A (PurityFiniteSetting.Line Y)).fixedDerived.functor.preimage
    ((compactSupportEncoding A c).hom.app _ ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).map (nativeIso A Y _).hom ≫
      (compactSupportSiteComparison (ULift.{u + 1} A) c).hom.app
        ⟨etaleValue A N hA Y, etaleValueUnshiftedPlus A N hA Y⟩ ≫
      (nu A (PurityFiniteSetting.Line Y)).map
        ((Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A) c).hom.app _ ≫
          (Etale.rightDerivedUpperShriekAdjunction (ULift.{u + 1} A)
            (PurityFiniteSetting.zeroSection Y)).counit.app _) ≫
      (nativeIso A (PurityFiniteSetting.Line Y) _).inv)

/-- The native constant coefficient sheaf, through the normalized section-action encoding.
Source: Step 4, the constant source of pur_s (blueprint: det-prop-a1). -/
def constantSheaf (T : Scheme.{u}) : Internal A T :=
  ((encoding A T).ordinary.trans (encoding A T).fixed).inverse.obj
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).obj
      (Etale.ordinaryFiniteConstant (ULift.{u + 1} A) T))

/-- The recorded degree-zero coefficient unit in native coordinates.
Source: Step 4 (blueprint: det-prop-a1). -/
abbrev unit (T : Scheme.{u}) :=
  native A T (Etale.constantComplex (ULift.{u + 1} A) T)

/-- The termwise encoding identifies this unit with its sheaf in degree zero.
Source: Step 4, single-complex normalization (blueprint: det-prop-a1). -/
def unitSingleIso (T : Scheme.{u}) :
    unit A T ≅ (DerivedCategory.singleFunctor _ 0).obj (constantSheaf A T) := by
  let E := (encoding A T).ordinary.trans (encoding A T).fixed
  letI : E.inverse.Additive :=
    inferInstanceAs ((encoding A T).fixed.inverse ⋙ (encoding A T).ordinary.inverse).Additive
  exact (encoding A T).fixedDerived.inverse.mapIso
      (((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
        T).mapDerivedCategorySingleFunctor 0).app _) ≪≫
    (E.inverse.mapDerivedCategorySingleFunctor 0).app _

/-- H0 of a derived orientation, with its constant source normalized in degree zero.
Source: Step 4, the displayed map of sheaves (blueprint: det-prop-a1). -/
def sheafMap (T : Scheme.{u}) (M : DerivedCategory (Internal A T))
    (m : unit A T ⟶ M) :
    constantSheaf A T ⟶ (DerivedCategory.homologyFunctor (Internal A T) 0).obj M :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (Internal A T) 0).inv.app _ ≫
    (DerivedCategory.homologyFunctor (Internal A T) 0).map ((unitSingleIso A T).inv ≫ m)

/-- The actual constant section one, before realization.
Source: Step 4, evaluation at one (blueprint: det-prop-a1). -/
def one (T : Scheme.{u}) (W : T.ProEtᵒᵖ) :
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).obj
      (Etale.ordinaryFiniteConstant (ULift.{u + 1} A) T)).obj.obj W :=
  ((constantSheafCompComparisonUpperStarIso
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).inv.app
      (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A))).hom.app W
    ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)))).app W (1 : ULift.{u + 1} A))

/-- Gamma(Y,H0(M)), a module carrier evaluated at the terminal pro-etale object.
Source: Step 4, the separate global assertion (blueprint: det-prop-a1). -/
abbrev sections (T : Scheme.{u}) (M : DerivedCategory (Internal A T)) :=
  (((encoding A T).ordinary.trans (encoding A T).fixed).functor.obj
    ((DerivedCategory.homologyFunctor (Internal A T) 0).obj M)).obj.obj
      (op (Scheme.ProEt.mk (𝟙 T)))

/-- The actual Hom-to-Gamma map, evaluating the induced sheaf map at one.
Source: Step 4 (blueprint: det-prop-a1). -/
def globalSection (T : Scheme.{u}) (M : DerivedCategory (Internal A T))
    (m : unit A T ⟶ M) : sections A T M :=
  (((encoding A T).ordinary.trans (encoding A T).fixed).functor.map
    (sheafMap A T M m)).hom.app (op (Scheme.ProEt.mk (𝟙 T)))
      ((((encoding A T).ordinary.trans (encoding A T).fixed).counitIso.inv.app _).hom.app
        (op (Scheme.ProEt.mk (𝟙 T))) (one A T _))

/-- The intrinsic coefficient-unit map is uniquely fixed by its value one in every
section. Its value is the actual associated-module-sheafification unit, not a basis.
Source: Steps 4--5, ordinary coefficient realization (blueprint: det-prop-a1).
Proof: the displayed ones form a compatible family. The free rank-one unit adjunction
extends them uniquely to a linear sheaf map. -/
theorem intrinsicUnitMap_existsUnique (T : Scheme.{u}) :
    ∃! f : SheafOfModules.unit _ ⟶
        (finiteCoefficientIntrinsicComparison T A).obj
          (Etale.ordinaryFiniteConstant (ULift.{u + 1} A) T),
      ∀ W : T.ProEtᵒᵖ, f.val.app W (1 : (Scheme.proEtaleConstantRing T A).obj.obj W) =
        (Scheme.sfRealizationUnit A T
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).obj
            (Etale.ordinaryFiniteConstant (ULift.{u + 1} A) T))).app W (one A T W) := by
  sorry

/-- The realized constant-ring equivalence, derived termwise.
Source: Step 5, the recorded finite exceptional functor (blueprint: det-prop-a1). -/
def intrinsicEncoding (T : Scheme.{u}) :=
  letI := (finiteCoefficientIntrinsicRealization_exact T A).1
  letI : (finiteCoefficientIntrinsicRealization T A).asEquivalence.functor.Additive :=
    finiteCoefficientIntrinsicRealization_additive T A
  (finiteCoefficientIntrinsicRealization T A).asEquivalence.mapDerivedCategory

/-- The canonical origin unit: comparison unit followed by the actual realization unit.
Source: Step 5, pur9's recorded composite (blueprint: det-prop-a1). -/
def originUnit (T : Scheme.{u})
    (K : DerivedCategory (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    K ⟶ (comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
      T).rightDerivedFunctor.obj ((intrinsicEncoding A T).inverse.obj
        ((finiteCoefficientIntrinsicDerivedComparison T A).obj K)) :=
  (derivedComparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).unit.app K ≫
    (comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).rightDerivedFunctor.map
      ((intrinsicEncoding A T).unitIso.hom.app _ ≫
        (intrinsicEncoding A T).inverse.map
          ((Functor.mapDerivedCategoryCompIso
            (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)
            (finiteCoefficientIntrinsicRealization T A)).inv.app K))

/-- The origin unit is invertible on bounded-below etale objects.
Source: Step 5, finite comparison (blueprint: det-prop-a1).
Proof: the realization unit is an equivalence unit. The etale-to-pro-etale derived
comparison unit is invertible on D+ by the published finite comparison theorem. -/
theorem originUnit_isIso (T : Scheme.{u})
    (K : DerivedCategory (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) (hK : DerivedCategory.TStructure.t.plus K) :
    IsIso (originUnit A T K) := by
  sorry

/-- Canonical etale Hom coordinates of a proposed native orientation after theta.
Source: Steps 1 and 5 (blueprint: det-prop-a1). -/
def etaleClass (N : ℕ) (hA : (N : ULift.{u + 1} A) = 0) (Y : Scheme.{u})
    (M : DerivedCategory (Internal A Y))
    (theta : M ≅ native A Y (etaleValue A N hA Y))
    (m : unit A Y ⟶ M⟦(2 : ℤ)⟧) :
    Etale.constantComplex (ULift.{u + 1} A) Y ⟶ (etaleValue A N hA Y)⟦(2 : ℤ)⟧ :=
  (Equiv.ofBijective _ (bijective_comparisonUpperStar_mapDerivedCategory_map
    (Etale.constantComplex (ULift.{u + 1} A) Y)
    ((etaleValue A N hA Y)⟦(2 : ℤ)⟧) (etaleValuePlus A N hA Y 2))).symm
      ((nativeIso A Y _).inv ≫
        (encoding A Y).fixedDerived.functor.map (m ≫ theta.hom⟦(2 : ℤ)⟧') ≫
        ((encoding A Y).fixedDerived.functor.commShiftIso (2 : ℤ)).hom.app _ ≫
        (nativeIso A Y _).hom⟦(2 : ℤ)⟧' ≫
        ((nu A Y).commShiftIso (2 : ℤ)).inv.app _)

/-- The supported representative in the shifted-coefficient localization triangle.
Source: Steps 3 and 6 (blueprint: det-prop-a1). -/
def supportedRepresentative (N : ℕ) (hA : (N : ULift.{u + 1} A) = 0) (Y : Scheme.{u})
    (g : Etale.constantComplex (ULift.{u + 1} A) Y ⟶
      (etaleValue A N hA Y)⟦(2 : ℤ)⟧) :=
  (Equiv.ofBijective _ (Etale.supportedClassMap_bijective (ULift.{u + 1} A)
    (PurityFiniteSetting.zeroSection Y)
    ((root A N hA (PurityFiniteSetting.Line Y))⟦(2 : ℤ)⟧))).symm
      (g ≫ ((Etale.rightDerivedUpperShriek (ULift.{u + 1} A)
        (PurityFiniteSetting.zeroSection Y)).commShiftIso (2 : ℤ)).inv.app _)

/-- The zero-section square is cartesian for every base map, without a finite-type
condition on the base map. Source: Step 6 (blueprint: det-prop-a1).
Proof: paste the affine-space base-change square with the two identities p s = 1;
cancel the cartesian lower square to obtain the square of zero sections. -/
theorem zeroSectionSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsPullback f (PurityFiniteSetting.zeroSection X) (PurityFiniteSetting.zeroSection Y)
      (AffineSpace.map (ULift.{u} (Fin 1)) f) := by
  sorry

/-- The normalized point condition compares with an independently constructed coordinate
Kummer boundary over the geometric point. Restriction uses the canonical counit mate for
supports and the root/pure-tensor coefficient comparison. Source: Step 6
(blueprint: det-prop-a1). -/
def GeometricallyNormalized (N : ℕ) (hN : 0 < N) (hA : (N : ULift.{u + 1} A) = 0)
    (Y : Scheme.{u}) (hr : IsUnit (N : Γ(PurityFiniteSetting.Line Y, ⊤)))
    (g : Etale.constantComplex (ULift.{u + 1} A) Y ⟶
      (etaleValue A N hA Y)⟦(2 : ℤ)⟧) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Y),
    let a := AffineSpace.map (ULift.{u} (Fin 1)) x
    let hr' : IsUnit (N : Γ(PurityFiniteSetting.Line (Spec (.of Ω)), ⊤)) := by
      simpa using hr.map a.appTop.hom
    Etale.restrictSupportedClass (ULift.{u + 1} A) a
      (PurityFiniteSetting.zeroSection Y) (PurityFiniteSetting.zeroSection (Spec (.of Ω)))
      x (zeroSectionSquare x)
      (Etale.leftDerivedUpperStarConstantComplexIso (ULift.{u + 1} A) a).inv
      (((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
        a).leftDerivedFunctor.commShiftIso (2 : ℤ)).app _ ≪≫
          (shiftFunctor _ (2 : ℤ)).mapIso (rootPullback A N hN hA a hr))
      (supportedRepresentative A N hA Y g) =
        Etale.shiftSupportedClass (ULift.{u + 1} A)
          (PurityFiniteSetting.zeroSection (Spec (.of Ω))) 2
          (etaleBoundary A N hN hA (Spec (.of Ω)) hr')

omit [Finite A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] in
/-- The degree-zero root input is bounded below.
Source: Step 1 (blueprint: det-prop-a1).
Proof: the derived single functor into the plus category gives this membership. -/
theorem rootPlus (N : ℕ) (hA : (N : ULift.{u + 1} A) = 0) (T : Scheme.{u}) :
    DerivedCategory.TStructure.t.plus (root A N hA T) := by
  sorry

end FiniteCoordinates

/-- The actual finite exceptional value used by pur9; the line has its canonical
composite structure map to the base field. Source: Step 5 (blueprint: det-prop-a1). -/
def finiteValue (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (k : Type u) [Field k]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (K : Scheme.proEtaleDerivedCategory (PurityFiniteSetting.Line Y)
      (Padic.coefficientExtensionRing l E n)) :=
  letI : (PurityFiniteSetting.Line Y).Over (Spec (.of k)) :=
    ⟨PurityFiniteSetting.lineProjection Y ≫ (Y ↘ Spec (.of k))⟩
  letI : LocallyOfFiniteType (PurityFiniteSetting.Line Y ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType
      ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  letI : QuasiCompact (PurityFiniteSetting.Line Y ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact
      ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  (Scheme.finiteExceptionalInverseImage l E n hn k Y (PurityFiniteSetting.Line Y)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj K

/-- Pur9's exceptional value at an etale root input is identified by the actual
comparison and realization units. This is a coordinate change, not a second support
construction. Source: Step 5 (blueprint: det-prop-a1). -/
def finiteValueIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (k : Type u) [Field k]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (N : ℕ) (hA : (N : ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) = 0) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    letI : TopologicalSpace (Padic.coefficientExtensionRing l E n) := ⊥
    letI := discreteTopology_bot (Padic.coefficientExtensionRing l E n)
    finiteValue l E n hn k Y
      ((finiteCoefficientIntrinsicDerivedComparison (PurityFiniteSetting.Line Y)
        (Padic.coefficientExtensionRing l E n)).obj
          (root (Padic.coefficientExtensionRing l E n) N hA (PurityFiniteSetting.Line Y))) ≅
      (finiteCoefficientIntrinsicDerivedComparison Y (Padic.coefficientExtensionRing l E n)).obj
        (etaleValue (Padic.coefficientExtensionRing l E n) N hA Y) := by
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E n) := ⊥
  letI := discreteTopology_bot (Padic.coefficientExtensionRing l E n)
  let B := Padic.coefficientExtensionRing l E n
  letI : (finiteCoefficientIntrinsicDerivedComparison Y B).CommShift ℤ :=
    inferInstanceAs (((finiteCoefficientIntrinsicComparison Y B).mapDerivedCategory).CommShift ℤ)
  let T := PurityFiniteSetting.Line Y
  let K := root B N hA T
  letI := originUnit_isIso B T K (rootPlus B N hA T)
  exact (finiteCoefficientIntrinsicDerivedComparison Y B).mapIso
    ((Etale.rightDerivedUpperShriek (ULift.{u + 1} B)
      (PurityFiniteSetting.zeroSection Y)).mapIso (asIso (originUnit B T K)).symm)

/-- Hom into the native Brown value, transported by its counit-normalized theta,
then by the recorded intrinsic coefficient comparison, to pur9's literal Hom group.
Source: Step 5 (blueprint: det-prop-a1). -/
def supportedClass (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (N : ℕ) (hA : (N : ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) = 0) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    letI : TopologicalSpace (Padic.coefficientExtensionRing l E n) := ⊥
    letI := discreteTopology_bot (Padic.coefficientExtensionRing l E n)
    ∀ (M : DerivedCategory (Internal (Padic.coefficientExtensionRing l E n) Y))
      (_theta : M ≅ native (Padic.coefficientExtensionRing l E n) Y
        (etaleValue (Padic.coefficientExtensionRing l E n) N hA Y)),
      (unit (Padic.coefficientExtensionRing l E n) Y ⟶ M⟦(2 : ℤ)⟧) →
        zeroSectionSupportedCohomology l E n hn k Y
          ((finiteCoefficientIntrinsicDerivedComparison (PurityFiniteSetting.Line Y)
            (Padic.coefficientExtensionRing l E n)).obj
              (root (Padic.coefficientExtensionRing l E n) N hA (PurityFiniteSetting.Line Y)))
          2 := by
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E n) := ⊥
  letI := discreteTopology_bot (Padic.coefficientExtensionRing l E n)
  let B := Padic.coefficientExtensionRing l E n
  letI : (finiteCoefficientIntrinsicDerivedComparison Y B).CommShift ℤ :=
    inferInstanceAs (((finiteCoefficientIntrinsicComparison Y B).mapDerivedCategory).CommShift ℤ)
  intro M theta m
  exact (intrinsicUnitIso B Y).hom ≫
    (finiteCoefficientIntrinsicDerivedComparison Y B).map (etaleClass B N hA Y M theta m) ≫
    ((finiteCoefficientIntrinsicDerivedComparison Y B).commShiftIso (2 : ℤ)).hom.app _ ≫
    (finiteValueIso l E n hn k Y N hA).inv⟦(2 : ℤ)⟧'

/-- The specific supported boundary in the recorded pur9 group, independently of any
proposed native orientation. Source: Steps 3 and 5 (blueprint: det-prop-a1). -/
def boundary (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (N : ℕ) (hN : 0 < N)
    (hA : (N : ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) = 0)
    (hr : IsUnit (N : Γ(PurityFiniteSetting.Line Y, ⊤))) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    letI : TopologicalSpace (Padic.coefficientExtensionRing l E n) := ⊥
    letI := discreteTopology_bot (Padic.coefficientExtensionRing l E n)
    zeroSectionSupportedCohomology l E n hn k Y
      ((finiteCoefficientIntrinsicDerivedComparison (PurityFiniteSetting.Line Y)
        (Padic.coefficientExtensionRing l E n)).obj
          (root (Padic.coefficientExtensionRing l E n) N hA (PurityFiniteSetting.Line Y))) 2 := by
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E n) := ⊥
  letI := discreteTopology_bot (Padic.coefficientExtensionRing l E n)
  let B := Padic.coefficientExtensionRing l E n
  letI : (finiteCoefficientIntrinsicDerivedComparison Y B).CommShift ℤ :=
    inferInstanceAs (((finiteCoefficientIntrinsicComparison Y B).mapDerivedCategory).CommShift ℤ)
  let T := PurityFiniteSetting.Line Y
  let g := Etale.supportedClassMap (ULift.{u + 1} B) (PurityFiniteSetting.zeroSection Y)
    (Etale.shiftSupportedClass (ULift.{u + 1} B) (PurityFiniteSetting.zeroSection Y) 2
      (etaleBoundary B N hN hA Y hr)) ≫
        ((Etale.rightDerivedUpperShriek (ULift.{u + 1} B)
          (PurityFiniteSetting.zeroSection Y)).commShiftIso (2 : ℤ)).hom.app _
  exact (intrinsicUnitIso B Y).hom ≫
    (finiteCoefficientIntrinsicDerivedComparison Y B).map g ≫
    ((finiteCoefficientIntrinsicDerivedComparison Y B).commShiftIso (2 : ℤ)).hom.app _ ≫
    (finiteValueIso l E n hn k Y N hA).inv⟦(2 : ℤ)⟧'

/-- The normalized orientation of the zero section, on the recorded Brown exceptional
inverse image, with literal pur9 supported cohomology and geometric normalization.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/det-prop-a1.md
and det-prop-a1.proof.md (blueprint: det-prop-a1).

Proof (the six steps of the node):
1. The positive finite quotient is killed by ell^n and its root line is constructible
   finite Tor. The zero section is closed with complement G_m. Over the arbitrary
   field k, Rs^! is the closed-case Brown right adjoint of def-pur-finite-closed-exceptional
   (no finite ell-CD hypothesis). Apply the closed-open localization triangle of
   lem-pur-support-localization-triangle. The canonical compact-support comparison chi
   and the unique counit-compatible theta of lem-sf-condensed-finite-exceptional-comparison
   replace the transported first vertex by this Brown exceptional value and the first
   arrow by its counit. Apply Rp_* and use ps = 1 and derived direct-image composition.
2. The finite twist is a perfect line (det-def-sp-tate-twist-locally-free). The perfect
   projection formula and det-prop-a1-kummer identify the middle term with A(1) and
   H0,H1 of the open term with A(1),A kappa(t); its other cohomology vanishes.
3. H0 restriction is the actual unit and is invertible. The long exact sequence gives
   only H2 of the unshifted exceptional value. The positive localization boundary
   carries kappa(t) to its free basis, giving the claimed sheaf isomorphism after [2].
4. Degree-zero normalization and fully faithful single complexes produce pur_s and
   identify its Hom group with maps from the coefficient unit to H0. Evaluation at
   one identifies those maps with Gamma, component by component.
5. The actual comparison units identify that Hom with the definition in pur9. Since
   theta intertwines the compact-support counits, it identifies entire localization
   triangles including their connecting arrows, so pur_s maps to boundary kappa(t).
6. Kummer and supported restriction commute with arbitrary base change, with the
   root/pure-tensor normalization. Thus at a geometric point the value is the
   independently constructed coordinate boundary there. Conversely the difference
   of two proposed maps is a section of the finite constant sheaf; if its value is
   zero at every geometric point, that section vanishes, on every component.
-/
theorem detPropA1 (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    let B := Padic.coefficientExtensionRing l E n
    letI := Padic.finite_coefficientExtensionRing l E n hn
    letI : TopologicalSpace B := ⊥
    letI := discreteTopology_bot B
    let YO : Over (Spec (.of k)) := Over.mk (Y ↘ Spec (.of k))
    letI : LocallyOfFiniteType YO.hom := inferInstanceAs
      (LocallyOfFiniteType (Y ↘ Spec (.of k)))
    letI : QuasiCompact YO.hom := inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
    letI : IsSeparated YO.hom := inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
    let XO : Over (Spec (.of k)) :=
      Over.mk (PurityFiniteSetting.lineProjection Y ≫ (Y ↘ Spec (.of k)))
    letI : LocallyOfFiniteType XO.hom := inferInstanceAs (LocallyOfFiniteType
      ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
    letI : QuasiCompact XO.hom := inferInstanceAs (QuasiCompact
      ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
    letI : IsSeparated XO.hom := inferInstanceAs (IsSeparated
      ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
    let s : YO ⟶ XO := Over.homMk (PurityFiniteSetting.zeroSection Y) (by
      change AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y ≫
        ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))) = _
      rw [← Category.assoc, AffineSpace.zeroSection_comp_over, Category.id_comp]
      rfl)
    letI : IsClosedImmersion s.left := zeroSectionClosed Y
    ∃ hA : ((l ^ n : ℕ) : ULift.{u + 1} B) = 0,
    ∃ hr : IsUnit ((l ^ n : ℕ) : Γ(PurityFiniteSetting.Line Y, ⊤)),
    ∃ hK : (constantModelBoundedConstructible (coefficient B) (PurityFiniteSetting.Line Y) ⊓
        DerivedCategory.finiteTorAmplitude _)
          (native B (PurityFiniteSetting.Line Y)
            (root B (l ^ n) hA (PurityFiniteSetting.Line Y))),
      let K : ConstantModelConstructibleFiniteTor (coefficient B)
          (PurityFiniteSetting.Line Y) := ⟨_, hK⟩
      let R := CondensedRing.finiteClosedCtfExceptionalInverseImage B l k s
        ⟨n, by
          have h := congrArg (fun z : ULift.{u + 1} B ↦ z.down) hA
          simpa only [ULift.down_natCast, ULift.zero_down, Nat.cast_pow]
            using h⟩
      let M := (R.obj K).obj
      ∃ theta : M ≅ native B Y (etaleValue B (l ^ n) hA Y),
        (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient B)
          (CondensedRing.compactificationOverField s)).map theta.hom ≫
            transportedCounit B (l ^ n) hA Y (CondensedRing.compactificationOverField s) =
          ((CondensedRing.finiteClosedCtfAdjunction B l k s
            ⟨n, by
          have h := congrArg (fun z : ULift.{u + 1} B ↦ z.down) hA
          simpa only [ULift.down_natCast, ULift.zero_down, Nat.cast_pow]
            using h⟩).counit.app K).hom ∧
        (∀ q : ℤ, q ≠ 0 → IsZero
          ((DerivedCategory.homologyFunctor (Internal B Y) q).obj (M⟦(2 : ℤ)⟧))) ∧
        Function.Bijective (globalSection B Y (M⟦(2 : ℤ)⟧)) ∧
        Function.Bijective (supportedClass l E n hn k Y (l ^ n) hA M theta) ∧
        ∃ pur : unit B Y ⟶ M⟦(2 : ℤ)⟧,
          supportedClass l E n hn k Y (l ^ n) hA M theta pur =
            boundary l E n hn k Y (l ^ n) (pow_pos (Fact.out : l.Prime).pos n)
              hA hr ∧
          IsIso pur ∧ IsIso (sheafMap B Y (M⟦(2 : ℤ)⟧) pur) ∧
          GeometricallyNormalized B (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) hA Y hr
            (etaleClass B (l ^ n) hA Y M theta pur) ∧
          ∀ phi : unit B Y ⟶ M⟦(2 : ℤ)⟧,
            GeometricallyNormalized B (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) hA Y hr
              (etaleClass B (l ^ n) hA Y M theta phi) ↔ phi = pur := by
  sorry

/-- The base-field finite-CD proof on the original recorded operation's domain.
Source: det-def-sf-operations (vi) (blueprint: det-prop-a1).
Proof: apply BaseFieldFiniteCD.of_finite or of_isAlgClosed according to hk. -/
theorem baseFiniteCD (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    (hk : Finite k ∨ IsAlgClosed k) : BaseFieldFiniteCD l k := by
  sorry

/-- The same orientation stated literally on the published ctfExceptionalInverseImage.
The general-field interface above has a canonical adjunction-compatible isomorphism
to this recorded operation; this corollary states every clause in its coordinates.
Source: det-prop-a1, all six steps (blueprint: det-prop-a1).
Proof: apply detPropA1 and conjugate its theta and orientation by
finiteClosedCtfExceptionalIso. Adjunction uniqueness preserves the counit equation,
so supported classes, the actual boundary, and the normalized point conditions agree.
The cohomology and Hom assertions transport along that same isomorphism. -/
theorem detPropA1_recorded (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] (hk : Finite k ∨ IsAlgClosed k)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    let B := Padic.coefficientExtensionRing l E n
    letI := Padic.finite_coefficientExtensionRing l E n hn
    letI : TopologicalSpace B := ⊥
    letI := discreteTopology_bot B
    let YO : Over (Spec (.of k)) := Over.mk (Y ↘ Spec (.of k))
    letI : LocallyOfFiniteType YO.hom := inferInstanceAs
      (LocallyOfFiniteType (Y ↘ Spec (.of k)))
    letI : QuasiCompact YO.hom := inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
    letI : IsSeparated YO.hom := inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
    let XO : Over (Spec (.of k)) :=
      Over.mk (PurityFiniteSetting.lineProjection Y ≫ (Y ↘ Spec (.of k)))
    letI : LocallyOfFiniteType XO.hom := inferInstanceAs (LocallyOfFiniteType
      ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
    letI : QuasiCompact XO.hom := inferInstanceAs (QuasiCompact
      ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
    letI : IsSeparated XO.hom := inferInstanceAs (IsSeparated
      ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
    let s : YO ⟶ XO := Over.homMk (PurityFiniteSetting.zeroSection Y) (by
      change AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y ≫
        ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))) = _
      rw [← Category.assoc, AffineSpace.zeroSection_comp_over, Category.id_comp]
      rfl)
    ∃ hA : ((l ^ n : ℕ) : ULift.{u + 1} B) = 0,
    ∃ hr : IsUnit ((l ^ n : ℕ) : Γ(PurityFiniteSetting.Line Y, ⊤)),
    ∃ hB : IsLocalizingAdmissibleCoefficient l (coefficient B),
    ∃ hK : (constantModelBoundedConstructible (coefficient B) (PurityFiniteSetting.Line Y) ⊓
        DerivedCategory.finiteTorAmplitude _)
          (native B (PurityFiniteSetting.Line Y)
            (root B (l ^ n) hA (PurityFiniteSetting.Line Y))),
      let K : ConstantModelConstructibleFiniteTor (coefficient B)
          (PurityFiniteSetting.Line Y) := ⟨_, hK⟩
      let R := CondensedRing.ctfExceptionalInverseImage (coefficient B) l k
        (baseFiniteCD l k hk) s hB
      let M := (R.obj K).obj
      ∃ theta : M ≅ native B Y (etaleValue B (l ^ n) hA Y),
        (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient B)
          (CondensedRing.compactificationOverField s)).map theta.hom ≫
            transportedCounit B (l ^ n) hA Y (CondensedRing.compactificationOverField s) =
          ((CondensedRing.ctfExceptionalAdjunction (coefficient B) l k
            (baseFiniteCD l k hk) s hB).counit.app K).hom ∧
        (∀ q : ℤ, q ≠ 0 → IsZero
          ((DerivedCategory.homologyFunctor (Internal B Y) q).obj (M⟦(2 : ℤ)⟧))) ∧
        Function.Bijective (globalSection B Y (M⟦(2 : ℤ)⟧)) ∧
        Function.Bijective (supportedClass l E n hn k Y (l ^ n) hA M theta) ∧
        ∃ pur : unit B Y ⟶ M⟦(2 : ℤ)⟧,
          supportedClass l E n hn k Y (l ^ n) hA M theta pur =
            boundary l E n hn k Y (l ^ n) (pow_pos (Fact.out : l.Prime).pos n)
              hA hr ∧
          IsIso pur ∧ IsIso (sheafMap B Y (M⟦(2 : ℤ)⟧) pur) ∧
          GeometricallyNormalized B (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) hA Y hr
            (etaleClass B (l ^ n) hA Y M theta pur) ∧
          ∀ phi : unit B Y ⟶ M⟦(2 : ℤ)⟧,
            GeometricallyNormalized B (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) hA Y hr
              (etaleClass B (l ^ n) hA Y M theta phi) ↔ phi = pur := by
  sorry


end WeilConjectures.AffineLineOrientation
