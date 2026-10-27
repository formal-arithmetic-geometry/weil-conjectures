module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Versality from tangent surjectivity and underlying ring lifts

Source: Stacks Project, Formal Deformation Theory, Tag 06IU (lemma-versal-criterion),
sufficient direction, and Tag 06J7 (lemma-RS-implies-S1-S2)
(blueprint: lem-sfb-artin-tangent-ring-lift-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

/-- Tangent surjectivity and the existence of underlying ring lifts for compatible
small-extension problems imply versality, including the prescribed isomorphism.
Source: Stacks Project, Formal Deformation Theory, Tags 06IU and 06J7
(blueprint: lem-sfb-artin-tangent-ring-lift-criterion).

Proof: first factor an arbitrary surjection into small extensions and an isomorphism,
using lem-sfb-artin-local-test-algebra. Transport along the final isomorphism and solve
successive small-extension problems, retaining the isomorphism supplied at each step.
For a small extension f : B → A, a : C → A, and α : f_*y ≅ ξ_a, the ring-lift
hypothesis supplies b : C → B; put y' = ξ_b and I = ker f.

Apply essential surjectivity of (RS) to P = B ×_A B and the triple (y', y, α⁻¹),
retaining its specified identification over A. This gives z over P. The difference
map g : P → k[I], (u,v) ↦ (residue(u), v-u), identifies P with B ×_k k[I],
since the maximal ideal of B kills I. Choose I ≃ k. Tangent surjectivity supplies
i : C → k[I] and an isomorphism τ : ξ_i ≅ g_*z. Compatibility at the residue
field follows from the predeformation condition.

By nilpotence of the target maximal ideals (lem-sfb-artin-local-test-algebra), b and i
factor through a common positive truncation D = C/m_C^n. It is Artinian local by
lem-weil-pbc-noetherian-local-quotient-artinian-local. Let h : D → B and j : D → k[I]
be the factorizations and x₁ the corresponding level of ξ. Applying (RS) to
D → B ← P gives w over Q = D ×_A B, identified compatibly with x₁ over D and z over P.

The map (u,v) ↦ (u,(residue(u),v-h(u))) identifies Q with D ×_k k[I]. The pair
(id_D,j) gives a section s : D → Q. Full faithfulness of (RS), applied to the
component isomorphisms id on x₁ and τ on its k[I] component, gives s_*x₁ ≅ w with
identity component over D. Pushing to B gives the corrected lift b' and y ≅ ξ_b'.
The identity component over D and the compatibility of w with z ensure that this
isomorphism restricts to precisely α. Composition solves the original surjection.
-/
theorem isVersal_of_tangent_surjective_of_ring_lifts
    {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k]
    [Algebra R k] [Algebra.FiniteType R k]
    (F : CofibredGroupoids.{u, v, w} R k)
    (hpre : IsPredeformation F) (hRS : IsRimSchlessinger F)
    (C : CompleteLocalAlgebra R k) (ξ : FormalObject F C)
    (htangent : Function.Surjective
      (fun a : LocalMap C (squareZeroTest (R := R) (k := k) k) ↦
        (Quotient.mk _ (evaluate ξ a) : tangentSet F)))
    (hring : ∀ (A B : TestCategory R k) (f : B ⟶ A), IsSmallExtension f →
      ∀ (a : LocalMap C A) (y : fibre F B)
        (_α : (push F f).obj y ≅ evaluate ξ a),
        ∃ b : LocalMap C B, (map f).comp b.hom = a.hom) :
    IsVersal ξ := by
  sorry

end AlgebraicGeometry.ArtinDeformation
