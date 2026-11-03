/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAffineGeometry
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-affine-integration). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Integration on the affine line is Rq_* of the open counit followed by the
projective trace whose Kummer Chern generator maps to +1. The compactification is
literally the standard chart; no arbitrary trace or orientation is introduced.
Source: affine-line integration (blueprint: def-pur-transport-affine-integration). -/
def ordinaryAffineIntegration (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) :=
  (Etale.ordinaryFinitePushforward A (ProjectiveLine Y ↘ Y)).map
    ((Etale.affineTraceOpenLeft A Y).map
      (Etale.ordinaryFiniteShiftedLinePullback A N hA
        (Etale.projectiveLineTraceTransport N hN A hA) (ProjectiveLine.affineChart Y)
        (affineTraceProjectiveInvertible N Y hY)).inv ≫
      (Etale.affineTraceOpenAdjunction A Y).counit.app
        ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine Y)) ⟦(2 : ℤ)⟧)) ≫
    Etale.ordinaryFiniteProjectiveLineTrace N hN A hA Y hY

end AlgebraicGeometry.ProEtale.PurityTransport
