/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefIntegralFiniteExtension
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange

/-! # The canonical finite relative trace

The finite trace is the absolute structural-counit transpose through support composition.
These are the unchanged finite constructions used by the integral scalar-transpose theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefDualFormulaScalarTranspose

/-- The specified proper/open support compositor, allowing supplied compactifications.
Source: blueprint Step 2, compact-support composition
(blueprint: def-coef-dual-formula-finite-trace). -/
def finiteSupportComposition (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hf : f ≫ g = h) [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    (c : Compactification f) (d : Compactification g) (e : Compactification h) :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ≅
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e := by
  subst h
  exact Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekIso A c) _ ≪≫
    Functor.isoWhiskerLeft _ (Etale.rightDerivedLowerShriekIso A d) ≪≫
    Etale.unboundedEtaleLowerShriekCompIso A f g ≪≫
    (Etale.rightDerivedLowerShriekIso A e).symm

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

/-- The finite relative trace is the absolute structural counit transposed through
compact-support composition. No exceptional-formula isomorphism is chosen here.
Source: blueprint Step 2, the defining equation for the absolute-trace transpose
(blueprint: def-coef-dual-formula-finite-trace). -/
def finiteEtaleTrace (n : ℕ) :
    (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).obj
      (finiteDualizingEtaleTerm l E D X n) ⟶ finiteDualizingEtaleTerm l E D Y n := by
  letI := c.hasCompactification
  letI := (finiteDualizingCompactification D X).hasCompactification
  letI := (finiteDualizingCompactification D Y).hasCompactification
  exact (finiteDualizingEtaleAdjunction l E D Y n).homEquiv _ _
    ((finiteSupportComposition (finiteDualizingCoeff l E n) f
      (Y ↘ Spec (.of D.k)) (X ↘ Spec (.of D.k))
      (CategoryTheory.comp_over f (Spec (.of D.k))) c (finiteDualizingCompactification D Y)
      (finiteDualizingCompactification D X)).hom.app
        (finiteDualizingEtaleTerm l E D X n) ≫ finiteDualizingEtaleCounit l E D X n)

/-- The finite absolute dualizing object is bounded below on the etale site.
Source: blueprint Step 1, finite Verdier duality
(blueprint: def-coef-dual-formula-finite-trace).
Proof: the coefficient unit is concentrated in degree zero. The bounded-below
exceptional adjoint preserves D+ over the Noetherian finite-dimensional base; apply
its D+ preservation theorem to that unit. -/
theorem finiteEtaleDualizing_plus (W : Scheme.{u})
    [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))] (n : ℕ) :
    DerivedCategory.TStructure.t.plus (finiteDualizingEtaleTerm l E D W n) := by
  let := (finiteDualizingCompactification D W).hasCompactification
  exact Etale.plus_rightDerivedUpperShriek_obj
    (finiteDualizingCoeff l E n) (W ↘ Spec (.of D.k)) _
    (Etale.boundaryCoefficientPlus (finiteDualizingCoeff l E n) (Spec (.of D.k))).property

/-- The etale-origin support comparison, in intrinsic finite coefficients.
Source: blueprint Steps 1--2, comparison-site realization
(blueprint: def-coef-dual-formula-finite-trace). -/
def finiteSupportOrigin (n : ℕ) :
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((finiteDualizingRealization l E X n).obj (finiteDualizingEtaleTerm l E D X n)) ≅
      (finiteDualizingRealization l E Y n).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).obj
            (finiteDualizingEtaleTerm l E D X n)) :=
  (ProEtale.sfIntrinsicCompactSupportComparison
    (Padic.coefficientExtensionRing l E (n + 1)) c).app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X).mapDerivedCategory.obj
          (finiteDualizingEtaleTerm l E D X n)) ≪≫
    (sfIntrinsicDerivedEquivalence Y
      (Padic.coefficientExtensionRing l E (n + 1))).functor.mapIso
        ((ProEtale.compactSupportSiteComparison (finiteDualizingCoeff l E n) c).app
          ⟨finiteDualizingEtaleTerm l E D X n, finiteEtaleDualizing_plus D l E X n⟩)

/-- The canonical finite relative trace after the prescribed site and coefficient transport.
Source: blueprint Step 2, absolute trace
(blueprint: def-coef-dual-formula-finite-trace). -/
def finiteTrace (n : ℕ) :
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      (integralDualizingFiniteTerm l E D X n) ⟶ integralDualizingFiniteTerm l E D Y n :=
  (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
      (finiteDualizingOrigin l E D X n).inv ≫
    (finiteSupportOrigin D l E f c n).hom ≫
    (finiteDualizingRealization l E Y n).map (finiteEtaleTrace D l E f c n) ≫
    (finiteDualizingOrigin l E D Y n).hom

end WeilConjectures.CoefDualFormulaScalarTranspose
