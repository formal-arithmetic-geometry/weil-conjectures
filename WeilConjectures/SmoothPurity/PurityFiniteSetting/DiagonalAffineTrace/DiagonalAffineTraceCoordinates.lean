/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleOrderedIntegration
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteTensorProjection
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTateCoordinates
public import WeilConjectures.AlgebraicGeometry.TensorTraceTranspose

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.Proper.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.Mathlib.CategoryTheory.NatIso

/-! # Diagonal affine trace and finite-level site comparison

Source: main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
cor-pur-dualizing-object-purity.md, Kummer normalization sentence
(blueprint: def-pur-diagonal-affine-trace-coordinates).

The auxiliary arrows only put the recorded ordered Kummer integrations in the
source coordinates of the actual diagonal purity map. The pro-etale integration
uses the independently constructed pro-etale coordinate counits. Every ordinary
presentation and every positive annihilating exponent is retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace
open AlgebraicGeometry.ProEtale.VectorIntegrationSite


section Ordinary
variable (A : Type (u + 1)) [CommRing A] [Finite A]
  (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
  (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)


/-- The tensor/normalized-root identification of the ordered right coefficient.
Source: the affine integration source identification
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def coefficientIso :
    (Etale.affineTraceRight A N hA S d).obj (Etale.ordinaryFiniteUnit A S) ≅
      Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d :=
  Etale.affineLinearCoefficientDescent A N hA
      (Etale.projectiveLineTraceTransport N hN A hA) S hS d ≪≫
    Etale.vectorIntegrationBaseCoefficientPullback A N hA
      (Etale.projectiveLineTraceTransport N hN A hA) (affineTraceProjection S d) hS d


/-- Canonical source transport to the ordered left/right tower; no trace occurs here.
Source: the compact-support and Tate identifications of the affine model
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def ordinarySourceIso :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).obj
        (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d) ≅
    (Etale.affineTraceLeft A S d).obj
      ((Etale.affineTraceRight A N hA S d).obj (Etale.ordinaryFiniteUnit A S)) :=
  (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).mapIso (coefficientIso A N hN hA S hS d).symm ≪≫
    (Etale.affineLinearCompactComparison N hN A hA S hS d).symm


/-- Ordered restriction of the normalized projective-line traces on the ordinary site.
Source: t_d^e in the affine-model statement
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def ordinaryTrace :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).obj
        (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d) ⟶
      Etale.ordinaryFiniteUnit A S :=
  (ordinarySourceIso A N hN hA S hS d).hom ≫
    Etale.affineTraceCounit A N hA (Etale.projectiveLineTraceTransport N hN A hA)
      (fun T _ hT ↦ Etale.projectiveLineTraceDatum N hN A hA T hT) S hS d


end Ordinary


section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true



end

section Finite
variable (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  (n : ℕ) (S : Scheme.{u}) [IsNoetherian S]
  (hS : IsUnit (C.l : Γ(S, ⊤))) (r : ℕ)
  (hA : ((C.l ^ (r + 1) : ℕ) : (Scheme.finiteTateCoefficient C.l E n)) = 0) (d : ℕ)


end Finite


end WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace
