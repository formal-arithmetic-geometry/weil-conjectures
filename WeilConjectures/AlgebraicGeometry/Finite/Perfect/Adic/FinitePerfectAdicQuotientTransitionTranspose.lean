/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransitionUnique

/-! # Transposes of the ordinary quotient arrows

Source: Stacks Project, Tags 06YY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The transpose of a consecutive quotient arrow under extension of scalars along the
consecutive quotient map is invertible. This is true but not yet formalized.
Source: Stacks Project, Tags 06YY and 09C6.

Proof sketch: by `hδ` and since sheafified pure tensors generate, the transpose sends
`s ⊗ (b ⊗ x)` to `s q(b) ⊗ x`; it is the balancing isomorphism
`A_n ⊗ (R_(n+1) ⊗ N) ≅ R_n ⊗ N`, restricted to the chart, where `φ` and `hcompat` identify
`A_n ⊗ R_(n+1)` with `R_n`. Its inverse sends `b ⊗ x` to `1 ⊗ (b' ⊗ x)` for a local lift `b'`
of `b`. -/
theorem finitePerfectAdicQuotientTransition_transpose_isIso
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (V : X.Etale) (n : ℕ)
    (δ : finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
      finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        finitePerfectAdicStepRestrict X d V n)
    (hδ : FinitePerfectAdicQuotientTransition X d φ V n δ) (N : CompletedAdicModules X d) :
    IsIso (((ProEtale.sheafExtendScalarsAdjunction
      (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
        V.left).homEquiv _ _).symm (δ.app N)) := by
  sorry

end AlgebraicGeometry.Scheme
