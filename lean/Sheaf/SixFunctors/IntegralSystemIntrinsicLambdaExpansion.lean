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

/-- The chosen and intrinsic lambda components expand into their factors.
Source: Stacks 0F7B and blueprint fix-prop-coherence.

Proof: Unfold the two lambda definitions. Components of an isomorphism composite are
the composites of its components. Whiskering on the left is evaluation, and
whiskering on the right maps the component through the direct functor.
Associator components are identities. Removing them gives each displayed
five-factor word. Finally unfold the actual diagram fields. This calculation
uses no canonical-bridge compatibility square.
(blueprint: lem-sf-integral-system-lambda-word-expansions). -/
theorem lambdaWord_expansions (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    let d := properOpenBridgeWord l E o c a b k r p i h M
    (d.f = d.a ≫ d.b ≫ d.c ≫ d.d ≫ d.e) ∧
      (d.g = d.x ≫ d.y ≫ d.z ≫ d.w ≫ d.n) := by sorry

end WeilConjectures.IntegralSystemRealization
