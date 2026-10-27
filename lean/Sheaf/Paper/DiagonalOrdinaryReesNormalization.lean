/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityDiagonalDualizingData
public import Sheaf.Paper.FiniteSmoothPurityMaps
import Sheaf.Paper.DiagonalOrdinaryReesEquation

/-! # From coordinate counits to the ordinary Rees normalization

Source: smooth-purity general-ring proof (2), comparison with the prime-power orientation.
(blueprint: lem-pur-diagonal-ordinary-rees-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- An ordinary orientation normalized by every ordered affine coordinate counit
over the bottom coefficient extension has the specified diagonal, Rees specialization
and integration normalization.

Source: blueprint/latest, sec-smooth-purity/sk-thm-smooth-purity/
sk-thm-smooth-purity-general-ring.proof.md, Proof (2), final paragraph, and
sec-smooth-purity/sk-prop-sp-orientation/thm-pur-diagonal-dualizing-object.proof.md.
(blueprint: lem-pur-diagonal-ordinary-rees-normalization).

Proof: apply finite-ring section deformation to the smooth first self-projection
and its closed diagonal section. It supplies kappa normalized at one and the
invertible specialization. The Rees quotient is the associated graded of the
diagonal ideal; its symmetric-algebra comparison gives the normal bundle and
an isomorphism over X, hence the square required in OrientationNormalized.
Form the ordinary composite of the inverse diagonal base-change identification,
this specialization, the inverse normal-section map, and inverse integration
adjunct. These factors are invertible by smooth base change, normalized section
deformation and vector-bundle purity. On centered etale smooth charts the section
coordinate-normalization equation identifies the specialization with the ordered
affine comparison. The normal-bundle integration adjunct has precisely the same
ordered affine counit, with its rank-one factor fixed by the Kummer trace.
Consequently this composite satisfies DiagonalOrientationNormalization. The given
e has that normalization too. After identifying both sources with the shifted
rank-one Tate sheaf, remove the common shift; full faithfulness of the single
functor and sheaf Hom gluing on smooth coordinate charts identify their maps.
Multiply this equality by the integration adjunct and the normal-section map to
obtain the displayed normalization equation. For d=0 the ordered tensor is empty
and each chart counit has its identity normalization. For empty X or the zero
coefficient ring the same argument takes place in the zero category. No scalar
extension, tensor formula, or exponent-independence assertion enters this lemma. -/
theorem diagonalOrdinaryReesNormalization (P : PurityFiniteSetting.{u})
    (hP : P.extension = ⊥)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (d : ℕ) (f : X ⟶ Y) [HasCompactification f]
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (G : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (e : Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f ≅
      P.diagonalTwistEtale X d)
    (he : P.DiagonalOrientationNormalization d f aY e) :
    Etale.FiniteSmoothPurity.OrientationNormalized P.Coefficient P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
      f d G (P.diagonalExponent_isUnit (f ≫ aY)) e := by
  let _ := G
  have _ := hP
  let hN : 0 < P.diagonalExponent :=
    pow_pos P.coefficients.prime.out.pos P.level
  let hX : IsUnit (P.diagonalExponent : Γ(X, ⊤)) :=
    P.diagonalExponent_isUnit (f ≫ aY)
  obtain ⟨κ, hκ, _⟩ :=
    AlgebraicGeometry.Etale.FiniteRingSectionDeformation.existsUnique_normalized
      P.diagonalExponent hN P.Coefficient P.diagonalExponent_annihilates hX d
      (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)
  let q := AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison
      (pullback.diagonal f) ≪≫
    AlgebraicGeometry.Etale.FiniteRingSectionDeformation.coneBundleIso d
      (pullback.fst f f) (pullback.diagonal f)
  have hq : q.hom ≫ VectorBundleZeroSection.π X d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) =
      Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f) := by
    dsimp [q]
    rw [Category.assoc,
      (AlgebraicGeometry.Etale.FiniteRingSectionDeformation.coneBundleIso_spec d
        (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)).1,
      (AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison_spec
        (pullback.diagonal f)).1]
    exact Scheme.Hom.purityNormalProjection_eq _ _ (pullback.diagonal_fst f)
  have sq : IsPullback q.hom
      (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
      (VectorBundleZeroSection.π X d
        (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by simpa using hq⟩
  exact ⟨κ, hκ, sq, by
    exact diagonalOrdinaryReesEquation P d f aY G e κ hκ sq he⟩

end WeilConjectures.PurityFiniteSetting
