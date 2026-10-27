/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage

/-! # Rational conjugacy of maximal split tori

Source: Milne, Algebraic Groups (2017), Theorem 25.10, printed p.546
(blueprint: lem-sfb-field-maximal-split-tori-conjugacy).

Maximality is tested among closed split tori over k. The conjugation identity is an
identity of scheme morphisms, so also holds on points over every commutative k-algebra.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Maximal split tori of a reductive group over an arbitrary field are conjugate by a
rational point, with conjugation restricting to an isomorphism over the original field.

Source: Milne, Algebraic Groups (2017), Theorem 25.10, printed p.546
(blueprint: lem-sfb-field-maximal-split-tori-conjugacy).

Proof plan:
1. First handle commuting closed split tori A and B. Multiplication A × B -> G is a
   homomorphism. The product has split-torus coordinates and is affine of finite type
   by lem-trf-lattice-torus-coordinates-action. By
   lem-sfb-affine-homomorphism-flat-image it factors faithfully flatly onto a closed
   subgroup I of G. By lem-sfb-field-split-torus-flat-quotient, I is split. Restriction
   to (a,1) and (1,b) factors both inclusions through I. If A and B are maximal split,
   these factorizations are isomorphisms, so A = I = B as subgroups of G. No assertion
   about surjectivity on rational points of the faithfully flat map is needed.
2. If every closed split torus is central, apply step 1 and take g = 1. Otherwise use
   lem-sfb-field-parabolic-isotropy-criterion to choose a proper minimal parabolic P.
   Its quotient X = G/P is proper of finite type and has the rational point q(1).
   By lem-sfb-field-parabolic-quotient-rational-lift, q is equivariant for the left
   action of G, and its identity fibre is P over every algebra.
3. Restrict the action to each S_i. By lem-sfb-split-torus-rational-fixed-point, X has
   an S_i-fixed rational point x_i. By lem-sfb-field-parabolic-quotient-rational-lift,
   lift it to h_i in G(k). Equivariance gives q(s*h_i) = q(h_i); acting by h_i^(-1)
   gives q(h_i^(-1)*s*h_i) = q(1), over every algebra. The identity-fibre property
   puts R_i = h_i^(-1)*S_i*h_i inside P, scheme-theoretically: apply it to the universal
   point of the affine S_i. Conjugation preserves splitness and maximality in G, hence
   R_i is also maximal split in P.
4. By lem-sfb-minimal-parabolic-split-centralizers, for L_i = C_G(R_i) there is
   u in (R_u P)(k) conjugating L_1 to L_2. Commutativity of R_1 gives R_1 contained
   in L_1, so u*R_1*u^(-1) is contained in L_2 = C_G(R_2). These two maximal split
   tori commute over every algebra; step 1 identifies them. Set g = h_2*u*h_1^(-1).
   Substitution gives g*S_1*g^(-1) = S_2. Conjugation, built from the group operations
   of def-sc-group-scheme, has inverse conjugation by g^(-1), and restricts to the
   asserted group-scheme isomorphism. Its inclusion identity is the displayed equality
   of morphisms, hence gives x ↦ g_B*x*g_B^(-1) for every algebra B. No extra field
   hypothesis was used, and the same argument includes rank zero. -/
theorem field_maximal_split_tori_conjugacy
    {k : Type u} [Field k] (G S₁ S₂ : Grp (Over (Spec (.of k))))
    (_hG : ReductiveTorusCentralizer.IsReductive G)
    (i₁ : S₁ ⟶ G) (i₂ : S₂ ⟶ G)
    [IsClosedImmersion i₁.hom.hom.left] [IsClosedImmersion i₂.hom.hom.left]
    (_hS₁ : ∃ r : ℕ, Nonempty (S₁ ≅ MultiplicativeType.splitTorus k r))
    (_hS₂ : ∃ r : ℕ, Nonempty (S₂ ≅ MultiplicativeType.splitTorus k r))
    (_hmax₁ : ∀ (T : Grp (Over (Spec (.of k)))) (j : T ⟶ G),
      IsClosedImmersion j.hom.hom.left →
        (∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r)) →
          ∀ a : S₁ ⟶ T, a ≫ j = i₁ → IsIso a)
    (_hmax₂ : ∀ (T : Grp (Over (Spec (.of k)))) (j : T ⟶ G),
      IsClosedImmersion j.hom.hom.left →
        (∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r)) →
          ∀ a : S₂ ⟶ T, a ≫ j = i₂ → IsIso a) :
    ∃ (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) (e : S₁ ≅ S₂),
      (toUnit S₁.X ≫ g) * i₁.hom.hom * (toUnit S₁.X ≫ g)⁻¹ =
        e.hom.hom.hom ≫ i₂.hom.hom := by
  sorry

end AlgebraicGeometry
