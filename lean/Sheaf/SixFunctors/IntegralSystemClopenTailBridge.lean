/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module

public import Sheaf.SixFunctors.IntegralSystemProperOpenBridgeWord

/-! A factor identity used in proper/open transport. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The clopen/compositor tail commutes with the canonical bridge.
Source: Stacks 0F7B and blueprint fix-prop-coherence.

Proof: Transport the inverse open unit by left-adjoint uniqueness. Its transpose under
the direct adjunction transports by conjugateIsoEquiv, giving the clopen square.
The normalized direct compositors agree on ordinary sections by pullbackComp;
conjugation and the prescribed cochain models lift the agreement to the derived
compositors. Equality induction handles the lift-composite equality. Map the
clopen square through the second projection, append this compositor square,
and use naturality of the direct bridge on the two component morphisms.
No cartesian or restriction factor is used.
(blueprint: lem-sf-integral-system-clopen-tail-bridge). -/
theorem clopenTail_bridge (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    let d := properOpenBridgeWord l E o c a b k r p i h M
    d.c ≫ d.d ≫ d.e ≫ d.v = d.j ≫ d.k ≫ d.z ≫ d.w ≫ d.n := by sorry

end WeilConjectures.IntegralSystemRealization
