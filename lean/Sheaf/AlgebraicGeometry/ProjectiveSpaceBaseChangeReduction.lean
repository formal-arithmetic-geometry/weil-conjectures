/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLinePower
public import Sheaf.AlgebraicGeometry.TorsionAbelianBaseChange

/-!
# Reduction of projective-space base change to the projective line

Source: Stacks Project, Tag 0A4F, last paragraph
(blueprint: lem-weil-pbc-reduction-projective-space).
-/

@[expose] public section

universe u_reduction

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Proper base change for every projective line implies proper base change for its fibre
powers and for every projective space, including dimension zero.
Source: Stacks Project, Tag 0A4F, last paragraph
(blueprint: lem-weil-pbc-reduction-projective-space).

Proof:
1. Projective-space projections are proper
   (lemma-nagata-projective-space-base-change-proper). Identity maps are finite and proper
   (lem-weil-pbc-isomorphism-finite, lem-weil-pbc-finite-proper); properness of fibre-power
   projections follows by base change and composition (lem-weil-pbc-proper-composition).
2. Convert PBC to injective acyclicity using lemma-weil-pbc-property-iff-acyclicity and
   def-weil-pbc-injective-acyclicity-property, then use prop-weil-pbc-composition-stability
   to obtain composition of PBC morphisms (Stacks 0A4D).
3. At zero the fibre-power projection is the identity, and the projective-space projection
   is an isomorphism (lem-weil-pbc-projective-space-zero-isomorphism). Both satisfy PBC by
   the finite case (prop-weil-pbc-finite-morphism; Stacks 0A4E).
4. Induct on the fibre power. Its first projection is a projective-line projection over the
   previous power up to an isomorphism (lemma-nagata-projective-space-base-change-pullback,
   def-pc-fibre-product). Apply the hypothesis over that scheme, the finite case for the
   isomorphism, and composition twice.
5. For positive n the symmetric-product map to Pⁿ is finite, surjective and over the base
   (lem-weil-pbc-symmetric-product-properties, lem-weil-pbc-symmetric-product-finite,
   lem-weil-pbc-symmetric-product-surjective, lem-weil-pbc-symmetric-product-over-base).
   It is proper and satisfies PBC by the finite case.
6. Cancel this proper surjection from its composite, the fibre-power projection, using
   lemma-weil-pbc-cancellation (Stacks 0A4C). This gives PBC for Pⁿ; step 3 covers zero. -/
theorem hasTorsionAbelianBaseChange_projectiveSpace_of_projectiveLine
    (_h : ∀ S : Scheme.{u_reduction}, HasTorsionAbelianBaseChange (ProjectiveLine S ↘ S))
    (T : Scheme.{u_reduction}) (n : ℕ) :
    IsProper (ProjectiveSpace.projectiveLinePower T n).hom ∧
      HasTorsionAbelianBaseChange (ProjectiveSpace.projectiveLinePower T n).hom ∧
      IsProper (ℙ(ULift.{u_reduction} (Fin (n + 1)); T) ↘ T) ∧
      HasTorsionAbelianBaseChange (ℙ(ULift.{u_reduction} (Fin (n + 1)); T) ↘ T) := by
  sorry

end AlgebraicGeometry.Etale
