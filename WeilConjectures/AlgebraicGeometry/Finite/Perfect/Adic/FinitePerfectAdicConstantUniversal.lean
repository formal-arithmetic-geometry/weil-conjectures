/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicLiftedTransitionUniversal
import WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizationArrowUniversal

/-! # Sourcewise universality of the constant finite perfect transition

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

/-- The explicit constant transition is universal after pullback to one etale source.

Source: Stacks Project, Tags 06YY, 093J and 09C6. -/
theorem finitePerfectAdicEtaleConstant_universal (Y : Scheme.{t})
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) (U : Y.Etale) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (etaleIsomorphismNormalizationArrow Y
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
        (finitePerfectAdicEtaleConstantTransition Y T n) U))) := by
  have h := finitePerfectAdicLiftedTransition_universal T n
  simpa [finitePerfectAdicEtaleConstantTransition] using
    (etaleNormalizationArrow_universal_of_constant Y
      (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
      (finitePerfectAdicLiftedTransition T n) h U)

end AlgebraicGeometry.Scheme
