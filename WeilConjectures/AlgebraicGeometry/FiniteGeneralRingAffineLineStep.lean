/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData

/-! # The last-coordinate comparison in the ordered affine tower

Source: general-ring smooth purity, proof (3), exponent independence.
(blueprint: def-sp-general-ring-affine-line-step).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
attribute [local implicit_reducible] affineTraceTower

/-- Pull the shifted line comparison from the original base to the preceding tower stage.
This is a composite of specified inverse-image isomorphisms, with no chosen witness.
Source: general-ring smooth purity, proof (3), exponent independence.
(blueprint: def-sp-general-ring-affine-line-step). -/
def finiteGeneralRingShiftedStageComparison
    (A : Type (u + 1)) [CommRing A] (M N : ℕ)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (T : Scheme.{u}) (hMunit : IsUnit (M : Γ(T, ⊤)))
    (hNunit : IsUnit (N : Γ(T, ⊤)))
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN) (d : ℕ) :
    (Etale.ordinaryFiniteLine A M hM (affineTraceTower T d))⟦(2 : ℤ)⟧ ≅
      (Etale.ordinaryFiniteLine A N hN (affineTraceTower T d))⟦(2 : ℤ)⟧ :=
  (Etale.ordinaryFiniteShiftedLinePullback A M hM tM
    (affineTraceProjection T d) hMunit).symm ≪≫
  (Etale.ordinaryFinitePullback A (affineTraceProjection T d)).mapIso
    ((shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso b)) ≪≫
  Etale.ordinaryFiniteShiftedLinePullback A N hN tN
    (affineTraceProjection T d) hNunit

/-- Compare the two last-coordinate right functors at a fixed complex.  The coefficient
comparison acts only on the shifted line, through the canonical line descent.
Source: general-ring smooth purity, proof (3), ordered affine induction.
(blueprint: def-sp-general-ring-affine-line-step). -/
def finiteGeneralRingAffineLineStep
    (A : Type (u + 1)) [CommRing A] (M N : ℕ)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (T : Scheme.{u}) (hMunit : IsUnit (M : Γ(T, ⊤)))
    (hNunit : IsUnit (N : Γ(T, ⊤)))
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN) (d : ℕ)
    (K : Etale.DerivedCategoryModule A (affineTraceTower T d)) :
    (Etale.affineTraceLineRight A M hM (affineTraceTower T d)).obj K ⟶
      (Etale.affineTraceLineRight A N hN (affineTraceTower T d)).obj K :=
  (Etale.affineLinearLineDescent A M hM tM (affineTraceTower T d)
    (affineTraceInvertible M T hMunit d) K).hom ≫
  (Etale.ordinaryFinitePullback A
    (AffineSpace PUnit.{u + 1} (affineTraceTower T d) ↘ affineTraceTower T d)).map
    (((Etale.ordinaryFiniteTensor A (affineTraceTower T d)).obj K).map
      (finiteGeneralRingShiftedStageComparison A M N hM hN tM tN T
        hMunit hNunit b d).hom) ≫
  (Etale.affineLinearLineDescent A N hN tN (affineTraceTower T d)
    (affineTraceInvertible N T hNunit d) K).inv

end AlgebraicGeometry.ProEtale
