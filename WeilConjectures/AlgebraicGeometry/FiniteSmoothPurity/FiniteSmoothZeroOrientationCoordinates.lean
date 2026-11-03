/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.Finite.Etale.FiniteEtaleDiagonalCoordinates
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteEtaleSectionIntegration
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization

/-! # Rank-zero orientation coordinates

Source: blueprint sec-smooth-purity/sk-prop-sp-orientation, three-factor formula
(blueprint: lem-pur-finite-smooth-zero-orientation-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The rank-zero geometric orientation, expressed at the coefficient unit.
Source: blueprint sec-smooth-purity/sk-prop-sp-orientation, its three-factor formula,
and sk-thm-smooth-purity, dimension-zero normalization
(blueprint: lem-pur-finite-smooth-zero-orientation-coordinates).

Proof: the diagonal of an etale map is clopen. Its normal projection is an
isomorphism, with inverse its zero section. On the clopen image the extended Rees
algebra is O_X[t]; on the complement it is O[t,t^-1]. The graph-normalized etale
sum adjunction therefore identifies the diagonal factor with the coefficient-unit
comparison. Its two fibre mates identify the deformation family with a constant
family. The comparison supplied by OrientationNormalized agrees with this
comparison by uniqueness of specialization normalized at one (finite-ring section
deformation). Rank-zero bundle integration is the identity-adjunction counit;
transport through the cone/bundle isomorphism identifies the last factor with the
same unit comparison. Substitute these identities in OrientationNormalized and
cancel the invertible bundle-section factor. The empty tensor is identified by
zeroLineIso, giving the equality of isomorphisms below. All computations apply on
each clopen piece, including the empty scheme and the zero coefficient ring. -/
theorem finiteSmoothZeroOrientationCoordinates
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] [Etale f]
    (d : ℕ) (hd : d = 0)
    (G : FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (hX : IsUnit (N : Γ(X, ⊤)))
    (alpha : dualizingComplex A f ≅ line A N hA X d)
    (hAlpha : OrientationNormalized A N hN hA f d G hX alpha)
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C) :
    alpha ≪≫ zeroLineIso A N hA X d hd = finiteSmoothOmegaCoordinates A C f := by
  let := G
  obtain ⟨kappa, hKappa, sq, hOrientation⟩ := hAlpha
  let b := FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA X hX d
    (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)
  let n := normalSectionMap A d (pullback.fst f f) (pullback.diagonal f)
    (pullback.diagonal_fst f) sq
  have : IsIso b := (FiniteRingSectionDeformation.bundleAdjoint_isIso N hN A hA X hX d
    (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)).2
  have : IsIso n := normalSectionMap_isIso A d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) sq N hN hA hX
  have hSection := finiteEtaleSectionIntegration A N hN hA (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) d hd hX C hC kappa hKappa sq
  have hDiagonal := finiteEtaleDiagonalCoordinates A f C hC
  have hAlphaHom : alpha.hom =
      (finiteSmoothOmegaCoordinates A C f).hom ≫ (zeroLineIso A N hA X d hd).inv := by
    apply (cancel_mono (b ≫ n)).mp
    calc
      alpha.hom ≫ (b ≫ n) = finiteSmoothDiagonalFactor A f ≫
          NoetherianSectionSpecialization.specialization A
            (pullback.fst f f) (pullback.diagonal f) kappa := hOrientation.symm
      _ = ((finiteSmoothDiagonalFactor A f ≫
          (finiteSmoothSectionCoordinates A C (pullback.fst f f)
            (pullback.diagonal f)).hom) ≫ (zeroLineIso A N hA X d hd).inv) ≫ (b ≫ n) := by
        rw [hSection]
        simp only [Category.assoc, b, n]
      _ = ((finiteSmoothOmegaCoordinates A C f).hom ≫
          (zeroLineIso A N hA X d hd).inv) ≫ (b ≫ n) := by rw [hDiagonal]
  apply Iso.ext
  simp only [Iso.trans_hom, hAlphaHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Etale.FiniteSmoothPurity
