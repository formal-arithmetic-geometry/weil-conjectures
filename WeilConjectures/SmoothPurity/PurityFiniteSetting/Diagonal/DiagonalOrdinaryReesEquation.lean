/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingData
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
public import WeilConjectures.AlgebraicGeometry.Finite.Smooth.FiniteSmoothGammaConstructions
public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization

/-! # The fixed-witness diagonal Rees equation

Source: smooth-purity general-ring proof (2), comparison with the prime-power
orientation (blueprint: lem-pur-diagonal-ordinary-rees-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale.NoetherianSectionSpecialization
open AlgebraicGeometry.Etale.FiniteSmoothPurity
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The coordinate-normalized orientation satisfies the displayed Rees equation
once the normalized section comparison and cone-to-bundle pullback square are fixed.

Source: blueprint/latest, sec-smooth-purity/sk-thm-smooth-purity/
sk-thm-smooth-purity-general-ring.proof.md, Proof (1)-(2), final paragraph.

Proof: use the normalized coordinate counit on the closed diagonal chart. The
DNC coordinate identity identifies its specialization with the fixed `kappa`,
while the vector-bundle chart equation identifies the remaining mate with the
inverse normal-section map and the actual integration adjunct. Pasting these
identities and cancelling the invertible locality and integration factors gives
exactly the displayed composite. The argument includes the empty chart and
rank-zero tensor (whose counit is the identity).
(blueprint: lem-pur-diagonal-ordinary-rees-equation).
-/
theorem diagonalOrdinaryReesEquation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (d : ℕ) (f : X ⟶ Y) [HasCompactification f]
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (G : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (e : Etale.dualizingComplex P.Coefficient f ≅
      P.diagonalTwistEtale X d)
    (κ : AlgebraicGeometry.Etale.NoetherianSectionSpecialization.family P.Coefficient
      (pullback.fst f f) (pullback.diagonal f) ≅
      (Etale.ordinaryFinitePullback P.Coefficient
        (AffineSpace (ULift.{u} (Fin 1)) X ↘ X)).obj
        (AlgebraicGeometry.Etale.sectionInvariant
          P.Coefficient (pullback.fst f f) (pullback.diagonal f)))
    (hκ : AlgebraicGeometry.Etale.NoetherianSectionSpecialization.Normalized P.Coefficient
      (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f) κ)
    (sq : IsPullback
      ((AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison (pullback.diagonal f) ≪≫
        AlgebraicGeometry.Etale.FiniteRingSectionDeformation.coneBundleIso d
          (pullback.fst f f) (pullback.diagonal f)).hom)
      (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
      (VectorBundleZeroSection.π X d
        (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)) (𝟙 X))
    (he : P.DiagonalOrientationNormalization d f aY e) :
    AlgebraicGeometry.Etale.finiteSmoothDiagonalFactor P.Coefficient f ≫
      AlgebraicGeometry.Etale.NoetherianSectionSpecialization.specialization P.Coefficient
        (pullback.fst f f) (pullback.diagonal f) κ =
      e.hom ≫
        AlgebraicGeometry.Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
          P.diagonalExponent (pow_pos P.coefficients.prime.out.pos P.level)
          P.Coefficient P.diagonalExponent_annihilates X
          (P.diagonalExponent_isUnit (f ≫ aY)) d
          (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) ≫
        normalSectionMap P.Coefficient d
          (pullback.fst f f) (pullback.diagonal f)
          (pullback.diagonal_fst f) sq := by
  sorry

end WeilConjectures.PurityFiniteSetting
