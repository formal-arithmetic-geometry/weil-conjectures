/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemFiniteLaws
/-! # Finite evaluation of the whole-system proper/open comparison

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md (2)
(blueprint: lem-route-field-shriek-system-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.FieldShriekSystem
/-- The normalized scalar and support coordinates satisfy the finite evaluation equation.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2), construction step 3
(blueprint: lem-route-field-shriek-system-evaluation).
Proof: first evaluate the proper adjunction mate. The restriction/pushforward square
is the identity on sections; its two ordinary transposes give the scalar/pullback
comparison. The PullComparison representative equation and the normalized scalar
transpose identify its localization with the finite pullback scalar comparison.
The tower geometry adjunction-evaluation theorem therefore identifies the evaluated
proper mate with the finite proper counit transpose. Next evaluate the open tensor
comparison. The open_unit equation says that its inverse is the open-unit mate of
the same pullback comparison. The open tensor normalization theorem identifies this
with the finite open tensor isomorphism. Whisker these two equations, use naturality
to move the scalar evaluation past the finite open and proper functors, and compose.
By the definition of reductionDirectImageComparison the resulting composite is the
right-hand side. The support coordinates have the identity-on-sections push map,
so their right-derived comparison is the same finite direct-image coordinate.
All these are equalities of natural transformations on the unbounded derived
categories: the representative argument uses flat-term K-flat resolutions of every
object. Thus the resulting equality applies to every M in the statement. -/
theorem field_shriek_evaluation_equation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (D : Models P)
    (scalarEvaluation : ∀ (E F : Index P) (h : E ≤ F) (T : Scheme.{u}) (n : ℕ),
      ScalarEvaluation P D h T n)
    (supportCoordinates : ∀ (E : Index P) (n : ℕ), FiniteCoordinates P E c n) :
    ∀ (E F : Index P) (h : E ≤ F) (n : ℕ)
    (M : SpTowerShriek.D P.coefficients.l E.val X),
    (SpTowerShriek.Ev P.coefficients.l F.val Y n).map ((comparison P D h c).app M) ≫
        (supportEvaluation P D F c n (supportCoordinates F n)).hom.app
          ((D.scalars E F h X).T.obj M) ≫
        (reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val n) c.i c.g).map
          ((scalarEvaluation E F h X n).iso.hom.app M) =
      (scalarEvaluation E F h Y n).iso.hom.app
          ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M) ≫
        (scalarExtensionFunctor ((D.coefficients E F h).quotient n) Y).map
          ((supportEvaluation P D E c n (supportCoordinates E n)).hom.app M) ≫
        (reductionDirectImageComparison ((D.coefficients E F h).quotient n) c.i c.g).app
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M) := by sorry
end AlgebraicGeometry.ProEtale.FieldShriekSystem
