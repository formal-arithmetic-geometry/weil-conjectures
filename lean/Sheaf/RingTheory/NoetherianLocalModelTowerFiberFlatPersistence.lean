module

public import Sheaf.RingTheory.NoetherianLocalModelTower
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

universe u v w t
open scoped TensorProduct
namespace Module

/-- Fibre flatness persists after a transition in a Noetherian local model tower.
Source: Stacks Project, Algebra, proof of Tag 00R7, second paragraph.
Base change, tensor associativity, and localization identify the later fibre module with
a localization of the base change of the earlier one, and localization preserves flatness.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-flat-persistence) -/
theorem NoetherianLocalModelTower.fiberFlat_of_le
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M]
    (X : NoetherianLocalModelTower R S S' M) :
    letI := X.preorder
    letI := X.commR
    letI := X.commS
    letI := X.localR
    letI := X.algRS
    letI := X.addN
    letI := X.moduleS
    ∀ (i j : X.ι), i ≤ j →
      Module.Flat
        (X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
          (IsLocalRing.maximalIdeal (X.R₀ i)))
        ((X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
          (IsLocalRing.maximalIdeal (X.R₀ i))) ⊗[X.S₀ i] X.N₀ i) →
      Module.Flat
        (X.S₀ j ⧸ Ideal.map (algebraMap (X.R₀ j) (X.S₀ j))
          (IsLocalRing.maximalIdeal (X.R₀ j)))
        ((X.S₀ j ⧸ Ideal.map (algebraMap (X.R₀ j) (X.S₀ j))
          (IsLocalRing.maximalIdeal (X.R₀ j))) ⊗[X.S₀ j] X.N₀ j) := by
  sorry

end Module
