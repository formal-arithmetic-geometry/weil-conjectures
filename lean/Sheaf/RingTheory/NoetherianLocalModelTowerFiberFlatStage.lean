module

public import Sheaf.RingTheory.NoetherianLocalModelTower
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

universe u v w t
open scoped TensorProduct
namespace Module

/-- Existence of one fibre-flat stage in a Noetherian local model tower.
Source: Stacks Project, Algebra, proof of Tag 00R7, second paragraph.
The proof constructs the quotient directed systems, identifies their colimits with the
closed fibre, and applies `RingTheory.exists_flat_stage`.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-flat-stage) -/
theorem NoetherianLocalModelTower.exists_fiberFlat_stage
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M]
    (X : NoetherianLocalModelTower R S S' M)
    (h_fibre : Module.Flat
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M)) :
    letI := X.preorder
    letI := X.commR
    letI := X.commS
    letI := X.localR
    letI := X.algRS
    letI := X.addN
    letI := X.moduleS
    ∃ i : X.ι, Module.Flat
      (X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
        (IsLocalRing.maximalIdeal (X.R₀ i)))
      ((X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
        (IsLocalRing.maximalIdeal (X.R₀ i))) ⊗[X.S₀ i] X.N₀ i) := by
  sorry

end Module
