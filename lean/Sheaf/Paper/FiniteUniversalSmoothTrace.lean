/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.SmoothTrace
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.SecSmoothPurity.FiniteGeneralRing
import Sheaf.Paper.FiniteFreeCoefficientExtension
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.DerivedPullbackTensorHom

import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.Paper.FiniteCoefficientDirectImage
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.Paper.FiniteCoefficientAdjointComparisons
import Sheaf.Paper.FiniteFreeProjectionExchange
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Sheaf.Paper.SfPreservationClass
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
import Sheaf.Paper.FiniteFreeCompactSupportComposition
import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Sheaf.Targets.VectorBundlePurity
import Sheaf.AlgebraicGeometry.VectorBundleIntegration
import Sheaf.Paper.VectorBundlePurity
import Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
import Sheaf.Paper.PurityDiagonalDualizingObject
import Sheaf.Paper.PuritySectionInvariantIntrinsic
import Sheaf.Paper.PurityDiagonalBaseChangeCompared
import Sheaf.Paper.PurityDncInvariance
import Sheaf.SecSmoothPurity.PurityDncCoefficientTransport
import Sheaf.Paper.SmoothPurityMap

/-! # Finite smooth trace and extension of coefficients

Source: main-20261015 blueprint, sec-smooth-purity/sk-thm-purity-transport,
proof Steps 1 and 3 (blueprint: lem-pur-finite-universal-smooth-trace).

The trace is the recorded normalized smooth trace. Its tensor-unit and shift
presentation is changed by canonical isomorphisms only. Both root comparisons
below retain the generator and derived-counit normalizations of the published API.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The prime-field stage in the same fixed coefficient closure, at positive level r.
Source: purity transport, A=Z/ell^r (blueprint: lem-pur-finite-universal-smooth-trace). -/
abbrev primeTraceSetting (P : PurityFiniteSetting.{u}) (r : ℕ) (hr : 1 ≤ r) :
    PurityFiniteSetting.{u} where
  field := P.field
  coefficients := P.coefficients
  extension := ⊥
  level := r
  level_pos := hr

/-- The recorded shifted coefficient line in intrinsic constant-ring coordinates.
Source: purity transport, T_A (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceTwist (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :=
  (sfIntrinsicDerivedEquivalence X P.Ring).functor.obj (P.diagonalTwist X d)

/-- Canonical pullback of the unit in the fixed module presentation: use the realization
unit, the site/pullback comparison and the ordinary constant-object comparison.
Source: purity transport, T_A (blueprint: lem-pur-finite-universal-smooth-trace). -/
def tracePulledUnitIso (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (P.smoothPurityPullback f).obj
        ((sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj (coefficientUnit P Y)) ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit P.Coefficient X) :=
  P.smoothPurityPullbackComparison f
      ((sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj (coefficientUnit P Y))
      (Etale.ordinaryFiniteUnit P.Coefficient Y)
      ((sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.app _) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        (Etale.ordinaryFiniteUnitPullback P.Coefficient f)


/-- Remove the constant unit in the ordinary presentation using its canonical left unitor.
Source: purity transport Step 2 (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceEtaleUnitIso (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule A X) :
    ((Etale.ordinaryFiniteTensor A X).obj (Etale.ordinaryFiniteUnit A X)).obj K ≅ K :=
  ((Etale.ordinaryFiniteTensor A X).mapIso
    (smoothPurityUnitIso A X)).app K ≪≫
    Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X K


/-- Transport the ordinary left unitor through the canonical site tensor comparison.
Source: purity transport Step 2 (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceComparedUnitIso (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :
    ((smoothPurityTensor P.Coefficient X).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient X))).obj (P.diagonalTwist X d) ≅
            P.diagonalTwist X d :=
  (smoothPurityComparisonTensor P.Coefficient X
      (Etale.ordinaryFiniteUnit P.Coefficient X) (P.diagonalTwistEtale X d)).symm ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        (traceEtaleUnitIso P.Coefficient X (P.diagonalTwistEtale X d))


/-- Remove the explicit unit factor in the trace's tensor presentation, using the
site/tensor comparison and the ordinary left unitor. No orientation is chosen.
Source: purity transport, T_A (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceTensorUnitIso (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : ℕ) :
    P.smoothPurityTensorSource f d (coefficientUnit P Y) ≅ P.diagonalTwist X d :=
  ((smoothPurityTensor P.Coefficient X).mapIso
      (tracePulledUnitIso P f)).app (P.diagonalTwist X d) ≪≫
    traceComparedUnitIso P X d


/-- The actual source object of smoothTrace, before removing its shifts and unit.
Source: recorded smooth trace (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceSource (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :=
  (sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
    ((((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj
        ((sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj (coefficientUnit P Y)))).obj
          ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧))⟦2 * (d : ℤ)⟧)


/-- Canonical identification of the recorded trace source with A_X(d)[2d].
Source: purity transport, unit-coefficient trace
(blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceSourceIso (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    traceSource P f d ≅ traceTwist P X d :=
  (sfIntrinsicDerivedEquivalence X P.Ring).functor.mapIso
    (P.smoothPurityReassociation X d
        ((P.smoothPurityPullback f).obj
          ((sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj (coefficientUnit P Y))) ≪≫
      traceTensorUnitIso P f d)


/-- The canonical extension of the shifted Tate line. First enlarge the prime-power
root exponent by the inverse of its normalized power-map comparison; then use the
coefficient extension fixed on scalar/root generators. Site realization supplies the
outside comparison. Source: purity transport Steps 1 and 3
(blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceTwistExtensionIso (P Q : PurityFiniteSetting.{u}) (φ : Q.Ring →+* P.Ring)
    (T : Scheme.{u}) (d : ℕ) (hA : (P.diagonalExponent : Q.Coefficient) = 0)
    (a : finiteEtaleTateLine T P.diagonalExponent Q.Coefficient hA ≅
      finiteEtaleTateLine T Q.diagonalExponent Q.Coefficient Q.diagonalExponent_annihilates)
    (σ : Etale.FiniteSmoothPurity.CoefficientLineComparison φ.ulift
      P.diagonalExponent P.diagonalExponent hA P.diagonalExponent_annihilates T) :
    (scalarExtensionFunctor φ T).obj (traceTwist Q T d) ≅ traceTwist P T d :=
  (reductionSiteScalarIso φ T).app (Q.diagonalTwistEtale T d) ≪≫
    (reductionSite P.Ring T).mapIso
      ((Etale.scalarExtension φ.ulift T).mapIso
          (finiteGeneralRingLevelPower Q.Coefficient P.diagonalExponent Q.diagonalExponent
            hA Q.diagonalExponent_annihilates T a d).symm ≪≫ σ.tensorPower d)

variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]


/-- The recorded normalized trace, expressed on the stated shifted Tate line.
Source: purity transport, t_A and t_B (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceOnTwist (d : ℕ) [SmoothOfRelativeDimension d f] :
    (smoothCompactSupport P f).obj (traceTwist P X d) ⟶ coefficientUnit P Y :=
  (smoothCompactSupport P f).map (traceSourceIso P f d).inv ≫ smoothTrace P f d


/-- Change only the direct-image presentation of the same chosen support functor.
The equality is fixed by the sectionwise coefficient adjunction, not chosen data.
Source: purity transport, compactification comparison
(blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceSupportModel :
    letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
    smoothCompactSupport P f ≅
      reductionCompactSupport P.Ring (HasCompactification.compactification f).i
        (HasCompactification.compactification f).g := by
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  exact Functor.isoWhiskerLeft
    (sfIntrinsicExtensionByZero
      (HasCompactification.compactification f).i P.Ring).mapDerivedCategory
    (eqToIso (reductionConstantPush_eq P.Ring (HasCompactification.compactification f).g).symm)

/-- The actual finite-free coefficient arrow on the same chosen compactification.
This is extension by zero followed by the proper tensor/counit mate.
Source: purity transport, c_{B/A,M}
(blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceCompactComparison (r : ℕ) (hr : 1 ≤ r)
    (φ : (primeTraceSetting P r hr).Ring →+* P.Ring)
    (M : proEtaleDerivedCategory X (primeTraceSetting P r hr).Ring) :
    (scalarExtensionFunctor φ Y).obj ((smoothCompactSupport (primeTraceSetting P r hr) f).obj M) ⟶
      (smoothCompactSupport P f).obj ((scalarExtensionFunctor φ X).obj M) :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  (scalarExtensionFunctor φ Y).map ((traceSupportModel (primeTraceSetting P r hr) f).hom.app M) ≫
    (reductionDirectImageComparison φ
      (HasCompactification.compactification f).i
      (HasCompactification.compactification f).g).app M ≫
    (traceSupportModel P f).inv.app ((scalarExtensionFunctor φ X).obj M)

/-- Multiplication-normalized extension of the coefficient unit, with the actual
site/scalar and realization comparisons.
Source: purity transport, A_Y tensor B = B_Y
(blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceUnitExtensionIso {Q : PurityFiniteSetting.{u}} (φ : Q.Ring →+* P.Ring)
    (T : Scheme.{u}) :
    (scalarExtensionFunctor φ T).obj (coefficientUnit Q T) ≅ coefficientUnit P T :=
  (reductionSiteScalarIso φ T).app (Etale.ordinaryFiniteUnit Q.Coefficient T) ≪≫
    (reductionSite P.Ring T).mapIso
      ((Etale.scalarExtension φ.ulift T).mapIso (smoothPurityUnitIso Q.Coefficient T) ≪≫
        Etale.ExceptionalCoefficients.unitIso φ.ulift T ≪≫
        (smoothPurityUnitIso P.Coefficient T).symm)


/-- Finite-free coefficient extension carries the normalized prime-power smooth trace
exactly to the normalized ramified trace, including its sign and shifted Tate line.
The existential comparison data are fixed by unitality and scalar/root generators;
they are presentations of the canonical identifications, not extra hypotheses.
Source: main-20261015 sk-thm-purity-transport, proof Steps 1 and 3
(blueprint: lem-pur-finite-universal-smooth-trace).

Proof plan:
1. Finite-free extension and scalar-extension preservation give B at level er and
   the same bounded constructible finite-Tor domain; compare ordinary and pro-etale
   constructible origins (lem-coef-finite-free-extension, det-sp-scalar-extension-functor,
   lem-sf-proetale-constructible-origin).
2. Balance the common root tower, use locally free Tate lines and commute even shifts;
   apply lem-pur-vector-integration-site-comparison to the actual integration maps.
3. On the common compactification use open extension by zero and the proper tensor
   counit mate to obtain the displayed coefficient map (lem-coef-finite-direct-image,
   lem-cbc-extension-zero-projection-formula, lem-sf-compact-support-restriction-of-scalars).
4. The finite exceptional comparison is the counit transpose, hence satisfies its
   counit equation (lem-pur-finite-coefficient-adjoint-comparisons).
5. Transport the actual projection, exchange and their inverses using
   lem-pur-finite-free-projection-exchange and thm-cbc-finite-level-proetale.
6. Transpose the tensor/counit formula for co-smoothness; its equality follows from
   the counit equation and naturality of the inverse projection formula.
7. Transport the unit-and-Kummer decomposition of the projective line; uniqueness of
   its mate fixes the positive normalized trace (lem-asd-ordinary-finite-p1-adjunction).
8. The geometric compositor obeys lem-pur-finite-free-compact-composition, on product
   compactifications as well as refinements.
9. Induct on ordered affine coordinates, with identity at zero, the projective-line
   trace at each successor and mate pasting for composition; all shifts are even.
10. Glue the degree-zero vector-bundle integration maps on trivializing opens;
    uniqueness identifies their scalar extensions (thm-amb-vector-bundle-purity).
11. Express the diagonal orientation by section base change, normalized deformation
    to the normal bundle and zero-section pullback of the vector orientation.
12. Apply lem-pur-dnc-coefficient-transport with R=A=Z/ell^r and target B: its
    counit-characterized comparison is the same mate as in step 4 (det-sp-reduction-exceptional),
    so its section comparisons are s^*b and the DNC arrow and the first section
    identification commute with coefficient extension.
13. The zero-section vector orientation commutes by steps 10 and 2; composing the three
    arrows gives alpha_B b = S(alpha_A) under S_Y A_Y = B_Y and S_X T_A = T_B.
14. Invert that orientation, tensor it with pullback of the unit and use the
    co-smoothness formula from step 6; thus the smooth purity map commutes
    (def-pur-smooth-purity-map, lem-weil-finite-compact-projection-formula).
15. Apply compact-support pushforward and then its counit. Naturality of the support
    comparison and step 4 cancel the exceptional comparison and give precisely the
    stated trace equation (def-pur-smooth-trace). -/
theorem finite_universal_smooth_trace
    (P : PurityFiniteSetting.{u}) (r : ℕ) (hr : 1 ≤ r)
    (_hlevel : P.level = P.ramificationIndex * r)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    ∃ (eA : (primeTraceSetting P r hr).Ring ≃+*
        ULift.{u} (ZMod (primeTraceSetting P r hr).diagonalExponent))
      (hB : ((primeTraceSetting P r hr).diagonalExponent : P.Ring) = 0)
      (hA : (P.diagonalExponent : (primeTraceSetting P r hr).Coefficient) = 0)
      (q : X.rootsOfUnitySheaf P.diagonalExponent ⟶
        X.rootsOfUnitySheaf (primeTraceSetting P r hr).diagonalExponent)
      (a : finiteEtaleTateLine X P.diagonalExponent
          (primeTraceSetting P r hr).Coefficient hA ≅
        finiteEtaleTateLine X (primeTraceSetting P r hr).diagonalExponent
          (primeTraceSetting P r hr).Coefficient
          (primeTraceSetting P r hr).diagonalExponent_annihilates)
      (σ : Etale.FiniteSmoothPurity.CoefficientLineComparison
        (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA).ulift
        P.diagonalExponent P.diagonalExponent hA P.diagonalExponent_annihilates X),
      FiniteGeneralRingKummerComparison (primeTraceSetting P r hr).Coefficient
        P.diagonalExponent (primeTraceSetting P r hr).diagonalExponent
        hA (primeTraceSetting P r hr).diagonalExponent_annihilates X q a ∧
      σ.roots = 𝟙 _ ∧
      (∀ M : proEtaleDerivedCategory X (primeTraceSetting P r hr).Ring,
        finiteTorConstructible (primeTraceSetting P r hr).coefficients.l
          (primeTraceSetting P r hr).extension
          r hr X M →
        IsIso (traceCompactComparison P f r hr
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA) M)) ∧
      traceCompactComparison P f r hr
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA)
          (traceTwist (primeTraceSetting P r hr) X d) ≫
        (smoothCompactSupport P f).map
          (traceTwistExtensionIso P (primeTraceSetting P r hr)
            (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA)
            X d hA a σ).hom ≫
        traceOnTwist P f d =
      (scalarExtensionFunctor
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA) Y).map
        (traceOnTwist (primeTraceSetting P r hr) f d) ≫
        (traceUnitExtensionIso P
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA) Y).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting
