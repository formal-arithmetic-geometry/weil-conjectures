module

public import Sheaf.SixFunctors.CompletedProjectionExchangeData

/-! # A step of the completed projection/base-change diamond

Source: blueprint fix-prop-coherence and fix-prop-projection-formula, projection diamond;
Stacks 0GL1 and 0E48 (blueprint: lem-sf-completed-projection-exchange-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.CompletedProjectionExchange

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {D : FiniteFieldDatum.{u}} (o : Operations l E) (ρ : Realizations l E D o)
  (Q : SixFunctorCompactifiedSquare D)

/-- The strict-system projection diamond with the normalized open restrictions
and the specified proper transposes, for arbitrary system objects.
Source: projection diamond, steps 7--10 of
lem-sf-completed-projection-exchange-realization; Stacks 0GL1 and 0E48
(blueprint: lem-sf-completed-projection-exchange-system).

Proof: on the simultaneous sequence-site K-flat models, pullback composition is
monoidal: both orders send a pure tensor to its two pulled-back factors, with
the same scalar balancing. Apply the inverse open projection and base-change
transpose formulas. Both open restrictions reduce to openSource using these
monoidal square identities and the open unit. Full faithfulness of open extension
then gives equality of the two open routes. The counit formulas for proper
projection and exchange, naturality of the square comparison and its monoidality
show that both proper transposes equal commonTranspose. Equivalently use
ringedExchangeTensorCoherence, retaining this common transpose. Expand the
compactification projection and exchange. Move the open projection across the
proper exchange by naturality; substitute the open equation and then the proper
equation. Finally use naturality of proper projection at the open base-change
map and tensor bifunctoriality. The result is exactly diamondRight, including
the inverse compactification compositor in each projection and the target square
comparison. This calculation takes place before coefficient evaluation or limit;
no projection or exchange is inverted. Identity and empty opens use the same unit
formulas, so no nonemptiness or Tor condition is needed.
-/
theorem completedProjectionExchangeSystem
    (M : System l E Q.X.obj.left) (N : System l E Q.Y.obj.left) :
    diamondLeft l E o ρ Q M N = diamondRight l E o ρ Q M N ∧
    OpenLaw l E o ρ Q M ((pull l E Q.p.hom.left).obj N) ∧
    ProperLaw l E o ρ Q ((Operations.shriek l E o Q.compactification.i).obj M) N := by sorry

end WeilConjectures.CompletedProjectionExchange
