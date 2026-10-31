/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IdentityCoefficientTransportData

/-! # Finite identity compact-support composition

The left-adjoint normalization step of identity-point coefficient transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

/-- The finite origin compositor agrees with the datum's canonical identity comparison.
Source: thm-sf-comp-composition, right identity clause, and the finite composition
and proper normalizations in def-sf-operation-stages
(blueprint: lem-sf-finite-identity-composition-normalization).

Proof: choose an etale-origin witness for a bounded constructible input. Apply
finiteCompositionNormalization with outer morphism the identity and the same
compactification for the composite, transported by comp_id. The witnessed origin
compositor is the image of originComposition_id_right. Substitute that unit law,
then the definition of the witness-support comparison. The adjacent inverse
realization and refinement comparisons cancel. finiteProperNormalization identifies
the remaining identity-compactification comparison with proper direct image;
the canonical direct-image identity gives precisely sfFiniteIdentityComparison.
Cancel the witness isomorphisms and reflect the equality through the fully faithful
constructible inclusion. The argument applies to every bounded constructible input,
including zero, and does not require a Tor bound on that input. -/
theorem finiteIdentityCompositionNormalization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorFiniteOperations D C E n hn) :
    @SfIdentityCompositionLaw.{u, u+2, u+2} D
      (sixFunctorFiniteCategory D C E n hn)
      (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C E n hn X)))
      S.finite (sfFiniteIdentityComparison D C E n hn S) := by
  sorry

end WeilConjectures
