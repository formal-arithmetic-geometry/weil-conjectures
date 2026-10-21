/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Paper.FiniteSmoothAdjunctionData

/-! # Dimension-zero normalization for finite smooth purity

Source: main-20261015, sec-smooth-purity/sk-thm-smooth-purity and
sk-lem-sp-reduction/compatibilities
(blueprint: lem-pur-finite-smooth-intrinsic-level-properties).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- Rank-zero normalization for a supplied geometric orientation.
Source: sk-thm-smooth-purity, dimension-zero normalization, and
sk-prop-sp-orientation, the diagonal/deformation/bundle factorization
(blueprint: lem-pur-finite-smooth-intrinsic-level-properties).
Proof: transport the finite smooth gamma normalization from its single universe lift of
Z/(ell^n) to the double lift used here along their canonical ring equivalence. Scalar
extension and restriction along this equivalence identify the coefficient units, roots
generators, derived tensor products and adjunction counits; uniqueness of their normalized
comparisons identifies the corresponding maps. Compare the supplied normalized
specialization with the one in this transported finite smooth gamma normalization.
Both restrict to the identity at one; uniqueness of normalized specialization
identifies them. For an etale morphism its diagonal normal bundle has rank zero. The canonical
cone-to-bundle comparison therefore identifies its section invariant with the coefficient unit,
and rank-zero bundle integration is the identity trace. Substituting these identifications
into OrientationNormalized gives the omega coordinates of the graph-normalized sum adjunction.
The tensor mate of that orientation is the inverse adjoint coordinate by
finite_smooth_gamma_normalization. The zero-fold ordered tensor is the unit via zeroLineIso,
so its source coordinate is exactly zeroSourceMap. This also applies to zero objects and empty
schemes. The trace equation is deduced separately from adjoint uniqueness in the level assembly. -/
theorem finiteSmoothIntrinsicLevelProperties
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (n : ℕ) (hn : 1 ≤ n)
    (G : FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (hX : IsUnit ((ell ^ n : ℕ) : Γ(X, ⊤)))
    (alpha : dualizingComplex (ModuleCat.{u + 1} (coefficient ell n)) f ≅
      line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d)
    (hAlpha : OrientationNormalized (coefficient ell n) (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) (CharP.cast_eq_zero _ _) f d G hX alpha) :
    let A := coefficient ell n;
    let N := ell ^ n;
    let hA : (N : A) = 0 := CharP.cast_eq_zero _ _;
    /- dimension_zero -/
    (∀ hd : d = 0, ∀ [Etale f],
      ∀ C : FiniteSmoothCompactSupportComparisons A, FiniteSmoothComparisonNormalized A C →
      ∀ K : DerivedCategoryModule A Y,
        gamma A f (line A N hA X d) alpha K ≫
            (finiteSmoothAdjointCoordinates A C f).hom.app K = zeroSourceMap A N hA f d hd K) := by
  sorry

end AlgebraicGeometry.Etale.FiniteSmoothPurity
