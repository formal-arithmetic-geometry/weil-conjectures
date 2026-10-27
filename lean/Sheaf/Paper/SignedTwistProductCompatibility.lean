/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.Paper.SignedTwistSiteTransportData
public import Sheaf.Paper.SignedLineScalarTensorTower

/-! # Products of evaluation-normalized finite Tate comparisons

Source: Stacks Project, Modules on Sites, Tags 03EL, 0GMX, 0FNY and 03EO.
(blueprint: lem-pur-signed-twist-product-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- Evaluation normalization and the positive root-tensor equations force the
mixed-sign product square for any normalized intrinsic product.
Source: Stacks 03EK (tensor products), 03EL and 03EO (tensor-Hom evaluation);
Step 3 of lem-pur-signed-twist-site-transport.
(blueprint: lem-pur-signed-twist-product-compatibility).

Proof: Work locally on a primitive-root chart, where the etale finite Tate line
has basis e. Its image under q(1) is a basis f of the pro-etale line. Positive
root-tensor normalization makes q(d) take the iterated basis tensor e_d to f_d,
including the coefficient unit at zero. The evaluation equation makes q(-d)
take the functional dual to e_d to the functional dual to f_d. These statements
hold after arbitrary pro-etale restriction because the normalization does.
On these signed bases the canonical etale ordered multiplication concatenates
positive tensors, multiplies negative duals, and contracts opposite pairs. It
always sends e_r tensor e_s to e_(r+s). This follows for opposite signs by
contracting min(abs(r),abs(s)) pairs, each of value one; zero degrees use the
unitors. The signed basis family satisfies SignedLineBasisPowers, so the assumed
normalization of mu sends f_r tensor f_s to f_(r+s). Inverse-image tensor
comparison preserves pure tensors. Thus the two routes agree on the basis
pair. Bilinearity extends equality to all local sections; sheaf separatedness
and gluing descend it. Changing e to u*e scales both routes by u^(r+s), so the
calculation is independent of the chosen primitive root and chart. This also
covers equal opposite exponents, the zero ring, and ell=2 without any sign. -/
theorem signedTwistProductCompatibility (P : PurityFiniteSetting.{u}) (n : ℕ)
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
    (he : P.SignedSiteEvaluation n hA q)
    (μ : P.SignedSiteProducts n)
    (hμ : ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)),
      SheafOfModules.SignedLineProductNormalized.{u + 1, u, u + 1}
        (R := integralCoefficientCommRingSheaf P.coefficients.l P.extension X n)
        (purTwistFiniteOne X P.coefficients.l P.extension n) (μ X a)) :
    P.SignedSiteMultiplication n hlevel hA μ q := by sorry

end WeilConjectures.PurityFiniteSetting
