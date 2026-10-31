/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothZeroOrientationCoordinates
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothOmegaTensorCoordinates

/-! # Dimension-zero normalization for finite smooth purity

Source: main-20261015, sec-smooth-purity/sk-thm-smooth-purity and
sk-lem-sp-reduction/compatibilities
(blueprint: lem-pur-finite-smooth-intrinsic-level-properties).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem tensorUnitCoordinates
    {D : Type*} [Category* D] {W L I P Q : D}
    (T : D ⥤ D) (a : W ≅ L) (e : L ≅ I) (r : T.obj I ≅ P)
    (rho : Q ≅ P) (omega : W ≅ I) (phi : T.obj W ⟶ Q)
    (ha : a ≪≫ e = omega)
    (h : r.inv ≫ T.map omega.inv ≫ phi = rho.inv) :
    (T.map a.inv ≫ phi) ≫ rho.hom = T.map e.hom ≫ r.hom := by
  have hfactor : T.map a.inv ≫ phi =
      (T.map e.hom ≫ r.hom) ≫ (r.inv ≫ T.map omega.inv ≫ phi) := by
    rw [← ha]
    simp only [Iso.trans_inv, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.map_hom_inv_id_assoc]
  rw [hfactor, h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Rank-zero normalization for a supplied geometric orientation.
Source: sk-thm-smooth-purity, dimension-zero normalization, and
sk-prop-sp-orientation, the diagonal/deformation/bundle factorization
(blueprint: lem-pur-finite-smooth-intrinsic-level-properties).
Proof: use hd to view the line in unit coordinates. The geometric lemma identifies alpha with
the graph-normalized omega coordinates after zeroLineIso. Tensor functoriality factors
gamma as zeroSourceMap followed by finiteSmoothGammaMap at that unit orientation:
the mapped inverse of zeroLineIso cancels its mapped hom, and the right unitor
cancels its inverse. The unit-orientation tensor normalization identifies the latter
map with the inverse adjoint comparison. Postcomposition with the adjoint comparison
cancels that inverse and leaves zeroSourceMap. This argument applies to every K,
including zero objects and empty schemes. The trace equation is deduced separately
from adjoint uniqueness in the level assembly. -/
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
    (alpha : dualizingComplex (coefficient ell n) f ≅
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
  intro A N hA hd _ C hC K
  let e := zeroLineIso A N hA X d hd
  let T := (derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((ordinaryFinitePullback A f).obj K)
  let r := derivedTensorRightUnitor (ModuleCat.{u + 1} A) X
    ((ordinaryFinitePullback A f).obj K)
  let rho := (finiteSmoothAdjointCoordinates A C f).app K
  let omega := finiteSmoothOmegaCoordinates A C f
  let phi := smoothTensorDualityMap A f
    (isIso_projectionMap_of_finite A f) K
  exact tensorUnitCoordinates T alpha e r rho omega phi
    (finiteSmoothZeroOrientationCoordinates A N
      (pow_pos (Fact.out : ell.Prime).pos n) hA f d hd G hX alpha hAlpha C hC)
    (finiteSmoothOmegaTensorCoordinates A f C hC K)

end AlgebraicGeometry.Etale.FiniteSmoothPurity
