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

/-- The cartesian and restriction prefix commutes with the canonical bridge.
Source: Stacks 0F7B and blueprint fix-prop-coherence.

Proof: On ordinary sections the bridges are the identity and the compositors are the
prescribed pullbackComp maps. Adjoint uniqueness identifies the corresponding
pull compositors. The cochain normalization lifts this identity to the derived
operations. Transport the unit defining beta and take its adjoint conjugate to
obtain the cartesian square. Transport the restriction factor by uniqueness of
open extension, its inverse open unit, and the normalized open compositor.
Map this square by the second-projection direct functor and paste with the
cartesian square. Naturality orders the source-coordinate bridge as displayed.
This argument uses no clopen comparison or final direct compositor.
(blueprint: lem-sf-integral-system-proper-open-prefix-bridge). -/
theorem properOpenPrefix_bridge (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    let d := properOpenBridgeWord l E o c a b k r p i h M
    d.a ≫ d.b ≫ d.j ≫ d.k = d.t ≫ d.t' ≫ d.x ≫ d.y := by sorry

end WeilConjectures.IntegralSystemRealization
