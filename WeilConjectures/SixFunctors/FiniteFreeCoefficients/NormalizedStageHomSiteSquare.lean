/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteEvaluation

/-!
# Normalized finite-stage internal-Hom site square

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
`lem-coef-finite-free-extension.proof.md`, paragraphs 1--2
(blueprint: lem-sf-normalized-stage-hom-site-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures
open WeilConjectures.FiniteFreeCoefficients

namespace WeilConjectures.FiniteFreeCoefficients

/-- The normalized internal-Hom comparison commutes with the etale/pro-etale comparison.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
`lem-coef-finite-free-extension.proof.md`, paragraphs 1--2
(blueprint: lem-sf-normalized-stage-hom-site-square).

The displayed equality is the sole assertion. The two tensor comparisons are retained as
explicit normalized data, while bounded constructibility and the common finite Tor interval
are hypotheses on both inputs. No invertibility of any internal-Hom or evaluation map is
asserted.

Proof: put H = RHom(K,M). Transpose both proposed composites under the pro-etale
tensor--Hom adjunction at nu(S K). Dinaturality of evaluation identifies the transpose
of Hom(sigma_K inverse, sigma_M) after any map f with sigma_M after the transpose of f,
precomposed with tensor(sigma_K inverse, identity). Expand the definition of the pro-etale
Hom comparison. Naturality of its inverse tensorator moves the scalar extension of beta
inside. The defining transpose equation for beta replaces evaluation after beta by nu
of etale evaluation after the inverse site tensor comparison. Naturality of sigma at
evaluation then leaves nu(S evaluation) after the inverse scalar/site tensor composite.
For the other side, expand beta at the target coefficient and use naturality of its
inverse site tensor comparison. The defining transpose equation for the etale Hom
comparison leaves the same final map nu(S evaluation), now after the other inverse
scalar/site tensor composite. Apply lem-sf-normalized-stage-site-monoidal-square to K,H
(the published adjunction uses K tensor H). Invert that equality of tensor isomorphisms
and cancel sigma_K against its inverse; the two preceding composites agree. Injectivity
of the adjunction bijection proves the asserted equality. The bounded constructible and
finite Tor hypotheses are retained from the node but are not needed by this calculation.
-/
theorem normalized_stage_hom_site_square
    (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (s t : Stage l E) (a : Arrow s t)
    (X : Scheme.{u}) (x : X ⟶ Spec (CommRingCat.of D.k))
    [LocallyOfFiniteType x] [QuasiCompact x] [IsSeparated x]
    (μet : Sites.TensorComparison false a.ringMap X)
    (hμet : Sites.NormalizedTensor false a.ringMap X μet)
    (μpro : Sites.TensorComparison true a.ringMap X)
    (hμpro : Sites.NormalizedTensor true a.ringMap X μpro)
    (K M : Sites.D false s.ring X)
    (hKc : Etale.DerivedCategory.isBoundedConstructible s.ring X K)
    (hMc : Etale.DerivedCategory.isBoundedConstructible s.ring X M)
    (c d : ℤ) (hcd : c ≤ d)
    (hKt : Etale.DerivedCategory.hasTorAmplitudeIn s.ring X c d K)
    (hMt : Etale.DerivedCategory.hasTorAmplitudeIn s.ring X c d M) :
    (Sites.scalar true a.ringMap X).map (Sites.siteHom s.ring X K M) ≫
      Sites.homMap true a.ringMap X μpro
        ((Sites.nu s.ring X).obj K) ((Sites.nu s.ring X).obj M) ≫
      homAction (Sites.hom true t.ring X)
        ((Sites.scalarSite a.ringMap X).inv.app K)
        ((Sites.scalarSite a.ringMap X).hom.app M) =
    (Sites.scalarSite a.ringMap X).hom.app
        (((Sites.hom false s.ring X).obj (op K)).obj M) ≫
      (Sites.nu t.ring X).map (Sites.homMap false a.ringMap X μet K M) ≫
      Sites.siteHom t.ring X
        ((Sites.scalar false a.ringMap X).obj K)
        ((Sites.scalar false a.ringMap X).obj M) := by
  sorry

end WeilConjectures.FiniteFreeCoefficients
