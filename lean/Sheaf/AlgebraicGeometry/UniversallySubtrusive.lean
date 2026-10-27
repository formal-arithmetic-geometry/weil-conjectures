module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.Spectral.ConstructibleTopology

/-! # Universally subtrusive scheme morphisms

Source: Rydh, Submersions and effective descent of étale morphisms, §1 and Definition (2.2).
(blueprint: def-sfb-universally-subtrusive-scheme-morphism)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- The scheme constructible topology, obtained locally from the constructible topologies of
all affine open charts. Using the final topology avoids any quasi-separatedness assumption.
Source: Rydh, §1, especially Proposition (1.2)(v).
(blueprint: def-sfb-universally-subtrusive-scheme-morphism) -/
@[instance_reducible]
def Scheme.localConstructibleTopology (X : Scheme.{u}) : TopologicalSpace X :=
  ⨆ (U : X.Opens) (_ : IsAffineOpen U),
    TopologicalSpace.coinduced (fun x : U => (x : X)) (constructibleTopology U)

/-- Universal subtrusiveness tested on all affine scheme base changes: the point map is a
quotient map in the locally defined constructible topologies, and every Zariski specialization
pair lifts. Quotient maps include surjectivity. The specialization direction is generic to
special. Source: Rydh, Definition (2.2), Proposition (2.1)(i), and Proposition (2.4).
(blueprint: def-sfb-universally-subtrusive-scheme-morphism) -/
def IsUniversallySubtrusive {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (T : Scheme.{u}) (_ : IsAffine T) (g : T ⟶ Y),
    @IsQuotientMap ↥(pullback f g : Scheme.{u}) T
      (Scheme.localConstructibleTopology (pullback f g)) (Scheme.localConstructibleTopology T)
      (pullback.snd f g) ∧
    ∀ t₀ t₁ : T, t₁ ⤳ t₀ →
      ∃ x₀ x₁ : (pullback f g : Scheme.{u}),
        pullback.snd f g x₀ = t₀ ∧ pullback.snd f g x₁ = t₁ ∧ x₁ ⤳ x₀

end AlgebraicGeometry
