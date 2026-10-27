/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Endomorphism

/-! # Scheme presentation of an admissible free finite action

Source: Stacks Project, spaces-properties.tex, Tag 07S6
(proposition-finite-flat-equivalence-global), invariant affine construction
(blueprint: lem-sfb-admissible-free-finite-quotient-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The invariant affine quotient charts glue to a scheme with the specified action
relation as its kernel pair. Only the etale presentation is asserted here: finiteness,
separatedness of the quotient, sheaf universality and geometric orbit fibres are
consequences established separately.

Source: Stacks Project, spaces-properties.tex, Tag 07S6
(proposition-finite-flat-equivalence-global), first and final proof paragraphs;
Spaces, Tags 02WW and 02WU; Groupoids, Tag 03BM
(blueprint: lem-sfb-admissible-free-finite-quotient-presentation).

Proof: Form the action groupoid on the coproduct of copies of M, with source the
fold and target on the g-summand the automorphism a(g). The unit, inversion and
composition are given on summands by 1, g inverse, and multiplication. Both
projections are etale since their restrictions to summands are isomorphisms;
freeness makes the relation monomorphic. Its etale relation quotient is an
algebraic space, with etale surjective atlas M and the specified kernel pair.
The hypothesis supplies an invariant affine neighborhood of every point.
The restricted relation is the finite coproduct of this affine open, hence affine,
and its projections are finite locally free: the fold is affine with coordinate
algebra the finite product, finite free on its coordinate idempotents. Apply the
affine quotient theorem 03BM to this relation. Its affine quotient maps by an open
immersion into the quotient sheaf by 02WU. The invariant opens cover M; etale local
lifts through M show that the quotient charts cover every test scheme. The scheme
representability criterion glues them to Q. The presentation theorem then supplies
etaleness, surjectivity and the prescribed kernel-pair square. For empty M the
empty collection of charts represents the empty scheme. No division by the order
of G, Noetherianity or finite-type assumption is used. -/
theorem exists_admissible_free_finite_quotient_presentation
    (M : Scheme.{u}) (G : Type v) [Group G] [Finite G]
    (a : G →* Aut M)
    [Mono (prod.lift (Sigma.desc (fun g : G ↦ (a g).hom))
      (Sigma.desc (fun _ : G ↦ 𝟙 M)))]
    (hcover : ∀ x : M, ∃ U : M.affineOpens,
      x ∈ U.1 ∧ ∀ g : G, (a g).hom ⁻¹ᵁ U.1 = U.1) :
    ∃ (Q : Scheme.{u}) (q : M ⟶ Q), Etale q ∧ Surjective q ∧
      IsPullback (Sigma.desc (fun g : G ↦ (a g).hom))
        (Sigma.desc (fun _ : G ↦ 𝟙 M)) q q := by sorry

end AlgebraicGeometry
