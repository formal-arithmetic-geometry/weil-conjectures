module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Gluing the affine embedded-point submodules

Source: Stacks Project, Divisors, Tag 02OL, proof of Lemma 31.5.8
(blueprint: lem-sc-hilbert-embedded-points-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Compatible finite submodules on an affine cover glue to a unique coherent
submodule, and the corresponding affine quotients glue to its cokernel.
Source: Stacks Project, Divisors, Tag 02OL, proof of Lemma 31.5.8
(blueprint: lem-sc-hilbert-embedded-points-gluing).

Proof:
1. On each affine open, identify the coherent module with the sheaf associated to
   its section module and localize the chosen finite submodule.
2. Compatibility on principal affine overlaps gives compatible restrictions, so the
   sheaf-gluing lemma produces a unique submodule and a monomorphism into `F`.
3. Finite generation is affine-local; local Noetherianity therefore makes the glued
   module coherent.
4. Restriction preserves cokernels, identifying the quotient sections with the
   local affine quotients.
-/
theorem existsUnique_coherent_submodule_of_affine_cover
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (I : Type u) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (N : ∀ i, Submodule (Γ(X, U i)) (Γ(F, U i)))
    (hN : ∀ i, Module.Finite (Γ(X, U i) : Type u) (N i))
    (Nloc : ∀ (i : I) (V : X.Opens),
      Submodule (Γ(X, V)) (Γ(F, V)))
    (hNloc : ∀ i, Nloc i (U i) = N i)
    (hcompat : ∀ (i j : I) (V : X.Opens), V ≤ U i → V ≤ U j →
      Nloc i V = Nloc j V) :
    ∃! K : Subobject F, (RingedSpace.IsCoherent X.toRingedSpace (K : X.Modules) ∧
      (∀ (i : I) (V : X.Opens), (AddSubgroup.map (K.arrow.app V).hom
        (Submodule.toAddSubgroup (⊤ : Submodule (Γ(X, V))
          (Γ((K : X.Modules), V)))) = (Nloc i V).toAddSubgroup)) ∧
      (∀ i, Nloc i (U i) = N i) ∧
      (∀ i, Nonempty (Γ((cokernel K.arrow : X.Modules), U i) ≃ₗ[Γ(X, U i)]
        (Γ(F, U i) ⧸ N i)))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
