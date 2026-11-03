/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-! # Shift compatibility of the scalar site mate

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`, Charts.
(blueprint: lem-sp-finite-affine-site-transport-right). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The site scalar mate commutes with the prescribed derived shift comparisons.

Source: Charts, shift compatibility of exact site transport in the latest
reduction-exceptional proof
(blueprint: lem-sp-finite-affine-site-transport-right).
Proof: transpose both paths under the derived scalar adjunctions. Their adjuncts
are equal by the signed-shift naturality of the scalar restriction/site square.
The unit and counit equations for leftAdjointUniq identify the chosen fixed scalar
left adjoints with the derived scalar adjoints, so the equality uses precisely
finiteAffineSiteScalarIso and the scalarShiftIso, rather than newly chosen maps. -/
theorem finiteAffineSiteTransportRight
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (b : ℤ) (K : DerivedCategoryModule A X) :
    L(ProEtale.sheafExtendScalars φ X).map
        ((Functor.commShiftIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory b).inv.app K) ≫
      (finiteAffineSiteScalarIso φ X).hom.app ((shiftFunctor _ b).obj K) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        ((FiniteSmoothPurity.scalarShiftIso φ X b).hom.app K) =
    (letI := φ.toAlgebra
     letI : L(ProEtale.sheafExtendScalars φ X).CommShift ℤ :=
       (ProEtale.leftDerivedSheafExtendScalarsAdjunction A B X).leftAdjointCommShift ℤ
     (L(ProEtale.sheafExtendScalars φ X).commShiftIso b).hom.app
       ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)) ≫
      (shiftFunctor _ b).map ((finiteAffineSiteScalarIso φ X).hom.app K) ≫
      ((Functor.commShiftIso
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory b).inv.app
        ((scalarExtension φ X).obj K)) := by
  sorry

end AlgebraicGeometry.Etale
