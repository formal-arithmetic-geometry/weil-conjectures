module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.TensorPullback

/-!
# Pushforward along a closed immersion is fully faithful

Source: Stacks Project, Modules, Lemma 08KS (modules-lemma-i-star-equivalence),
quoted for schemes in Morphisms, Lemma 01QY
(blueprint: lem-weil-pbc-closed-immersion-pushforward-fully-faithful).
-/

@[expose] public section

universe w

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- For a closed immersion, pullback followed by pushforward has invertible counit,
and pushforward is fully faithful
(blueprint: lem-weil-pbc-closed-immersion-pushforward-fully-faithful).
Proof: compute the counit on stalks using the quotient description of a closed
immersion and the tensor pullback stalk formula; then apply the adjunction theorem
that an isomorphism counit makes the right adjoint fully faithful.
-/
theorem closedImmersion_pushforward_fullyFaithful
    {X Z : Scheme.{w}} (i : Z ⟶ X) [IsClosedImmersion i] :
    let e : Scheme.Modules.tensorPullback i ⊣ Scheme.Modules.pushforward i :=
      Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
    (∀ (G : Z.Modules), IsIso (e.counit.app G)) ∧
      ∀ (G G' : Z.Modules),
        Function.Bijective (fun (φ : G ⟶ G') => (Scheme.Modules.pushforward i).map φ) := by
  sorry

end AlgebraicGeometry
