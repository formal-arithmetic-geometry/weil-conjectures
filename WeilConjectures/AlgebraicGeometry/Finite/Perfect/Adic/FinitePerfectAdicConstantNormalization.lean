/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantUniversal
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCoherence

/-! # Universal normalization of the explicit constant quotient diagram

Source: Stacks Project, Tags 06YY, 093J and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The specified constant algebraic transition is universal on every etale source,
with its canonical coefficient and restriction coherence. It constructs no descended
actual quotient, realization functor, or map of Isom presheaves.

Source: Stacks Project, Tags 06YY, 093J and 09C6. -/
theorem finitePerfectAdicEtaleConstant_normalization (Y : Scheme.{t})
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :
    EtaleUniversalNormalization Y
      (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
      (finitePerfectAdicEtaleConstantTransition Y T n) := by
  refine ⟨?_, ?_⟩
  · intro U
    exact finitePerfectAdicEtaleConstant_universal Y T n U
  · intro U V f
    exact finitePerfectAdicEtaleConstant_coherence Y T n f

end AlgebraicGeometry.Scheme
