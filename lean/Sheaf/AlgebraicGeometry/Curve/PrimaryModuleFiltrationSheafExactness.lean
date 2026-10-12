/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker R3
-/
module

public import Sheaf.AlgebraicGeometry.Curve.PrimaryModuleFiltrationFixedFieldComparison

/-!
# Quotient comparison for a single invariant subgroup inclusion

Source: Stacks Project, Tags 04JQ and 03QT; blueprint `lem-sc-affine-generic-second`,
proof paragraphs 1--2.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits ZeroObject Opposite
namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tags 04JQ and 03QT; blueprint
`lem-sc-affine-generic-second`, proof paragraphs 1--2.
(blueprint: lem-sc-primary-subgroup-sheaf-exactness)

Proof: The inclusion of A into B is injective. Its quotient is B/A, explicitly the
quotient of B.toIntSubmodule by the comap of A.toIntSubmodule under the subtype map.
For g in H, the hypothesis g*x-x in A says the induced action on B/A is the identity.
Thus the projection to primaryTrivialQuotient is equivariant. Its kernel is precisely
A and it is surjective, giving a short exact sequence of discrete H-modules. All
stabilizers in A and B are restrictions of open ambient stabilizers; those in the
trivial quotient are the whole group. The equivalence C.inverse preserves the
kernel and cokernel universal properties and therefore exactness, monomorphisms and
epimorphisms. Pullback across the scheme isomorphism e is an equivalence of sheaf
categories and does the same. The cokernel of the resulting inclusion is consequently
isomorphic to the associated sheaf of this specific quotient. The complex in the
conclusion was constructed from precisely this inclusion and its cokernel projection.
This works when A=B or B=0: the quotient and its associated sheaf are zero. No finiteness,
prime, filtration, initial stage or terminal comparison is used. -/
theorem primarySheafSequence_shortExact
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (H : OpenSubgroup (Gal(Ks/K))) (C : PrimaryFixedFieldEquivalence K Ks H)
    (hC : PrimaryFixedFieldComparison K Ks H Ω C)
    (T : Scheme.{u}) (e : Spec (.of (IntermediateField.fixedField H.toSubgroup)) ≅ T)
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (A B : AddSubgroup R.obj.V) (hle : A ≤ B)
    (hA : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ A →
      R.obj.ρ (g : Gal(Ks/K)) x ∈ A)
    (hB : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ B →
      R.obj.ρ (g : Gal(Ks/K)) x ∈ B)
    (htriv : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ B →
      R.obj.ρ (g : Gal(Ks/K)) x - x ∈ A) :
    (primarySheafSequence K Ks H Ω C T e R A B hle hA hB).ShortExact ∧
    Nonempty ((primarySheafSequence K Ks H Ω C T e R A B hle hA hB).X₃ ≅
      primaryAssociatedSheaf K Ks H Ω C T e (primaryTrivialQuotient K Ks H R A B)) := by
  sorry

end AlgebraicGeometry.Scheme
