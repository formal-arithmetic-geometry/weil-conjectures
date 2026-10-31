/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalPurityScalarModels

/-! # Normalized finite-stage PBC purity adjunctions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [QuasiCompact f] [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

attribute [local instance high] Algebra.toModule ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom
  pbcRationalScalarHom pbcPurityTwisted pbcPurityCompact
  pbcPurityTwistedAmbient pbcPurityCompactAmbient
  pbcPurityTateModel pbcPurityDerivedScalarModel purCoefficientModel
  integralSheafTwist completedDerivedScalarExtension pbcTateAmbient purScalarModel
  integralTwistOrdinaryBeta pbcPurityTateScalarModel pbcPurityTateScalarComponent
  pbcActualCompletedPull

attribute [local irreducible] pbcPurityStageTwisted pbcPurityStageCompact
  pbcPurityStageA pbcPurityStageC

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
    [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
    [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
    [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
    [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
    [fbase : f.IsOver (Spec (.of D.k))] [fsep : IsSeparated f]
    [fft : LocallyOfFiniteType f] [fsm : SmoothOfRelativeDimension d f]

include Xbase Ybase Xsep Ysep Xft Xqc Yft Yqc fbase fsep fft fsm hl in
/-- The finite-stage purity adjunctions have the prescribed compact-support mate.

Source: current blueprint sk-prop-sp-rational, rational-adjunction proof (1), and
sk-thm-purity-transport, coefficient-change proof (2)--(3); the original parent
prop-pur-rational-purity-transitivity-summands, Steps 1--3.
(blueprint: lem-pur-pbc-finite-purity-adjunction).

Proof: identify the PBC integral lattice category with the complete finite-Tor
category using integralStratifiedPerfectCharacterization and integral_residue_tor.
Use the simultaneous integral purity family of adicPurityScalarNaturality.
Transport the compact-support/exceptional adjunction along its purity isomorphism;
this makes completed pullback followed by Tate tensor and [2d] a right adjoint.
The integral coefficient square and counit-mate equation give compatibility of
these transported counits with the specified proper/open scalar comparison.
The completed coefficient model is fixed at each finite projection, and the Tate
and derived scalar model comparisons are the section-normalized ones, so the
comparison on the right-adjoint side is exactly pbcPurityTwistedScalar, rather
than an independently chosen comparison. Localize the linear integral Hom
bijections at the uniformizer. Their units, counits and triangle equations
localize as well; all rational objects are integral representatives and all
arrows are scalar fractions, so naturality holds on the entire raw categories.
Finally conjugate the coefficient equation by pbcPurityScalarNormalization at
both endpoints. Its defining integral components identify the localized square
with the displayed equation for StageA and StageC. The construction works for
identity and ramified extensions, zero inputs and empty schemes. -/
theorem pbcPurityFiniteAdjunction :
    ∃ adj : ∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcPurityStageCompact l Ω f c d E ⊣ pbcPurityStageTwisted l Ω f c d E,
    ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
      (K : pbcStageCategory l Ω Y E),
      (pbcPurityStageCompact l Ω f c d F).map
          ((pbcPurityStageA l Ω f c d h).hom.app K) ≫
          (adj F).counit.app (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj K) =
        (pbcPurityStageC l Ω f c d h).inv.app
            ((pbcPurityStageTwisted l Ω f c d E).obj K) ≫
          ((pbcScalarSystem l Ω Y dY.out iY.out).T h).map ((adj E).counit.app K) := by
  sorry

end AlgebraicGeometry.Scheme
