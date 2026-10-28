module

public import Sheaf.Paper.AmbientPullbackSiteData

/-! Componentwise sequence-site coefficient pullback.
Source: Stacks 03CB and 0941.
(blueprint: lem-sf-ambient-coefficient-pullback-iso-sequence-app).

The finite-stage comparisons are evaluated on each object of the product site.
Their compatible inverses give the componentwise inverse of the sequence map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- Every component of the sequence coefficient pullback is invertible.

Source: Stacks 03CB and 0941 (finite/sequence coefficient comparison).
Proof: evaluate the sequence-site adjunction at a product object `(n,U)`.  The
component is the finite-stage coefficient comparison at index `n`; its inverse
is the finite-stage inverse transported along the product projection.  The
finite inverses commute with all quotient transition maps, so they assemble to
a morphism on the sequence site and satisfy both inverse equations componentwise.
(blueprint: lem-sf-ambient-coefficient-pullback-iso-sequence-app) -/
theorem coefficientPullback_none_isIso_app {X Y : Scheme.{t}}
    (f : X ⟶ Y) (U : Site X none) :
    IsIso ((ringMap ell E f none).hom.app (op U)) := by
  sorry

end WeilConjectures.AmbientPullbackTensor
