/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The open equality locus of two relatively finite open subschemes

Source: Stacks Project, More on Groupoids in Spaces, Tag 04PK,
`lemma-finite-diagonal`, proof, for scheme test objects
(blueprint: lem-sfb-finite-open-equality-locus).

The two base-changed open subschemes are encoded by their inverse-image opens
in the ambient scheme fibre product. Unique factorization through the open
complement expresses representation of the equality subfunctor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The images of the two differences of relatively finite open subschemes form a
closed subset of the base. Its open complement represents their equality after
arbitrary scheme base change. The last equivalence states the representing
property by unique factorization through the canonical open immersion `V.ι`.
No separatedness assumption on the ambient morphism is needed.

Source: Stacks Project, More on Groupoids in Spaces, Tag 04PK,
`lemma-finite-diagonal`, proof, for scheme test objects
(blueprint: lem-sfb-finite-open-equality-locus).

Proof:
1. Each difference is closed in its own open subscheme, since the intersection
   of the two opens is open there. The finite restricted morphisms are closed
   maps by lem-weil-pbc-finite-closed-map-finite-fibres, so their images have
   closed union D. Its complement V is open. The affine-open basis
   (lem-weil-pbc-affine-opens-basis) supplies the scheme structure on this
   restricted locally ringed space, as in def-pc-scheme and def-weil-open-immersion.
2. For a test map h, put P = M ×_T T' and let r, s be its projections. The maps
   Z_i ×_T T' → P are base changes of the open inclusions: the pullback property
   follows by combining the map to Z_i with the composite to T'. Thus they are
   open immersions by lem-weil-pbc-open-immersion-base-change. Their opens are
   r⁻¹(Z_i), by lem-weil-pbc-base-change-image on these squares.
3. Their symmetric difference is the union E of the inverse images of the two
   original differences. Apply lem-weil-pbc-base-change-image to P for each
   difference to obtain s(E) = h⁻¹(D). A set is empty exactly when its image
   under a function is empty. Therefore the two base-changed opens agree if
   and only if h has image in V. Equality of opens is equality of their
   induced open subschemes, whose sheaves are restrictions of the ambient sheaf.
4. By lem-weil-pbc-morphism-factors-through-open-subscheme, image containment
   in V is equivalent to unique factorization through V.ι. This identifies
   maps to V with maps to T satisfying the equality. Precomposing a factorization
   gives a factorization of the precomposed map; uniqueness makes these
   identifications natural. Hence V.ι represents the equality subfunctor. -/
theorem finite_open_equality_locus {M T : Scheme.{u}} (q : M ⟶ T) (Z₁ Z₂ : M.Opens)
    [IsFinite (Z₁.ι ≫ q)] [IsFinite (Z₂.ι ≫ q)] :
    IsClosed (q '' ((Z₁ : Set M) \ (Z₂ : Set M)) ∪
      q '' ((Z₂ : Set M) \ (Z₁ : Set M))) ∧
    ∃ V : T.Opens,
      (V : Set T) = (q '' ((Z₁ : Set M) \ (Z₂ : Set M)) ∪
        q '' ((Z₂ : Set M) \ (Z₁ : Set M)))ᶜ ∧
      (∀ (T' : Scheme.{u}) (h : T' ⟶ T),
        Set.range h ⊆ (V : Set T) ↔
          (pullback.fst q h) ⁻¹ᵁ Z₁ = (pullback.fst q h) ⁻¹ᵁ Z₂) ∧
      (∀ (T' : Scheme.{u}) (h : T' ⟶ T),
        (pullback.fst q h) ⁻¹ᵁ Z₁ = (pullback.fst q h) ⁻¹ᵁ Z₂ ↔
          ∃! k : T' ⟶ V.toScheme, k ≫ V.ι = h) := by
  sorry

end AlgebraicGeometry
