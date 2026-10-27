/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.Paper.SignedTwistSiteTransportData

/-! # The dual extension of finite Tate site comparisons

Source: Stacks Project, Modules on Sites, Tags 03EL, 0GMX, 0FNY and 03EO.
(blueprint: lem-pur-signed-twist-evaluation-extension)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- The prescribed nonnegative comparison extends uniquely by the actual dual
pairings. No multiplication or geometric coherence is asserted here.
Source: Stacks 0GMX (pullback of internal Hom), 0FNY (finite locally free dual),
03EL and 03EO; Step 2 of lem-pur-signed-twist-site-transport.
(blueprint: lem-pur-signed-twist-evaluation-extension).

Proof: The root exponent is invertible on X, so each positive etale power is a
locally free line. Identify comparison inverse image of the constant coefficient
ring with the pro-etale coefficient ring. For each positive power L(d), the
finite-free dual-pullback comparison is an isomorphism. Compose it with
precomposition by the inverse of b(d). This gives the required negative map;
retain b at every nonnegative integer. The defining transpose equation evaluates
a pulled functional on b(d)(x) to the pulled coefficient phi(x). Restriction of
this equation gives the stated formula on every pro-etale test over an etale
object. The fixed-coefficient and ring-sheaf presentations have the same sections
and pairings through constant scalar restriction. To prove uniqueness, trivialize
L(d) locally. Its dual basis must map to the functional taking value one on the
image basis, hence is determined. Linearity gives equality on the chart and
separatedness gives equality of the negative sheaf maps. Adjunction detects
maps out of comparison inverse image, so these local equations determine the
isomorphisms. Function extensionality gives uniqueness of the whole family.
This includes degree zero and the empty scheme. -/
theorem signedTwistEvaluationExtension (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hlevel : P.level = n + 1)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (b : ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (k : ℕ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X (k : ℤ)) ≅ P.signedSitePro n X (k : ℤ))
    (hb : ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (k : ℕ),
      IsFiniteTateSiteComparison P.coefficients.l P.extension n X n hA k (b X a k)) :
    ∃! q : ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (r : ℤ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X r) ≅ P.signedSitePro n X r,
      (∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (k : ℕ),
        q X a k = b X a k) ∧ P.SignedSiteEvaluation n hA q := by sorry

end WeilConjectures.PurityFiniteSetting
