module

public import Sheaf.Paper.AmbientPullbackSiteData

/-! Finite-stage component of ambient coefficient pullback.
Source: Stacks 03CB and 03D3.
(blueprint: lem-sf-ambient-coefficient-pullback-iso-finite).

The proof compares the chosen ringed-site adjunction with the constant-sheaf
adjunction on the pro-etale terminal object.  The two left adjoints are uniquely
isomorphic, and the defining constant-section equation identifies that comparison
with `ringMap`; its component is therefore invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- Finite coefficient pullback is invertible.
(blueprint: lem-sf-ambient-coefficient-pullback-iso-finite) -/
theorem coefficientPullback_some_isIso {X Y : Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) :
    IsIso (ringMap ell E f (some n)) := by sorry

end WeilConjectures.AmbientPullbackTensor
