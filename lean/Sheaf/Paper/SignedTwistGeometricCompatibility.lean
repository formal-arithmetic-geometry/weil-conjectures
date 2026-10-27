/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.Paper.SignedTwistSiteTransportData

/-! # Geometric pullbacks of evaluation-normalized finite Tate comparisons

Source: Stacks Project, Modules on Sites, Tags 03EL, 0GMX, 0FNY and 03EO.
(blueprint: lem-pur-signed-twist-geometric-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- The evaluation-normalized signed family has the canonical geometric
pullbacks and the negative comparison square, with identity and composition.
Source: Stacks 03EL, 0GMX and 09A5; Step 4 of
lem-pur-signed-twist-site-transport.
(blueprint: lem-pur-signed-twist-geometric-compatibility).

Proof: The positive root-induced pullback maps and their comparison squares
follow from the same-root site square and the projection-induced finite-root
identification of lem-amb-tate-root-projection-reduction. Tensor iteration gives
the nonnegative comparison squares. For each negative power use pullback of the finite locally free
dual, followed by precomposition with the inverse positive geometric map. The
dual-pullback transpose equation proves geometric evaluation compatibility.
Pair each route of the negative comparison square with the common positive
route. Naturality of the canonical comparison mate and the positive comparison
square turn both evaluations into the same pulled etale evaluation. On a local
basis both negative routes therefore carry the basis functional to the unique
functional with value one on the pulled positive basis. Linearity and gluing
prove the square, with exactly the specified comparison mate. For an identity,
the dual of the positive identity evaluates identically to the upperStarId map;
for a composite, both candidate negative maps pair with the same composite
positive map to the same coefficient pullback. The same uniqueness gives the
upperStarComp law. Positive identity and composition are already those of
root-induced pullback. At degree zero use the constant coefficient comparison.
All constructions use the universal property of finite reduction and the root
tower; no interchange of inverse image with an infinite limit is required. -/
theorem signedTwistGeometricCompatibility (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hlevel : P.level = n + 1)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (b : ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (k : ℕ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X (k : ℤ)) ≅ P.signedSitePro n X (k : ℤ))
    (hb : ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (k : ℕ),
      IsFiniteTateSiteComparison P.coefficients.l P.extension n X n hA k (b X a k))
    (q : ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (r : ℤ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X r) ≅ P.signedSitePro n X r)
    (hq : ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (k : ℕ),
      q X a k = b X a k)
    (he : P.SignedSiteEvaluation n hA q) :
    ∃ τ : P.SignedSiteGeometric n,
      P.SignedSiteGeometricLaws n τ ∧ P.SignedSitePullbackSquare n hlevel hA τ q := by sorry

end WeilConjectures.PurityFiniteSetting
