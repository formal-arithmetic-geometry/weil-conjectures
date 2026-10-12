module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- (blueprint: lem-exc-galois-point-action-open).

Open stabilizers for the action on geometric étale lifts.

(source: Stacks Project, Tag 03QW, discussion before Theorem 59.56.3;
 blueprint: lem-exc-galois-point-action-open).

For an action obtained by precomposition with extensions of Galois automorphisms, a lift
factors through the finite separable residue field of its image point.  The subgroup fixing
that finite intermediate field is open in the Krull topology and fixes the lift.  The full
stabilizer is a union of its translates and is therefore open.
-/
theorem galoisPointAction_open_stabilizers
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (ρ : Gal(Ks/K) →* End (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber)
    (hρ : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (_ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale)
      (x : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X),
      ((ρ g).app X x).left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left) :
    ∀ (X : (Spec (.of K)).Etale)
      (x : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X),
      IsOpen {g : Gal(Ks/K) | (ρ g).app X x = x} := by
  sorry

end AlgebraicGeometry.Scheme
