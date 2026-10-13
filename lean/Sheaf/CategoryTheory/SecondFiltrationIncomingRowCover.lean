/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients

/-! # Incoming graded differential of an extended row

Source: Stacks Project, Homology, Tag 0130, clause 2.
(blueprint: lem-sp-second-filtration-incoming-row-cover).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- In positive resolution degree, the incoming graded differential is covered
by the incoming row term.
Source: Stacks Project, Tag 0130, clause 2, the second-filtration differential.
(blueprint: lem-sp-second-filtration-incoming-row-cover).

Proof. Put n = s+r and project the diagonal coproduct in degree n-1 onto
its summand with second coordinate s. This projection kills the next filtration
step. For r>0, lift the diagonal inclusion of the extended row term r-1
through the step s and then take its graded class. The projection descends to
the quotient and is inverse to this class: on the generating summand s the
composite is identity, and the other summands factor through step s+1 and
vanish. The interval is [s,n-1], so negative s is allowed. Composing with the
extension isomorphism identifies this source with row degree prev r = r-1.
The resulting e is an isomorphism, hence epic. Compute the total differential
on this inclusion. Its resolution component is the row differential and its
component raising s factors through step s+1. The latter vanishes after the
graded projection. Monicity of the step inclusion identifies the target lift
with the prescribed a, proving the displayed square.
A zero row is handled by the same projection/lift calculation, using the
unique morphisms between zero objects. No sign condition on s is used.
This statement concerns terms and differentials only, with no cycles,
filtered boundaries, or homology quotient.
-/
theorem secondFiltration_incoming_row_cover
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p)
    (r : ℕ) (s : ℤ) (hr : 0 < r)
    (a : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).X r ⟶
      (L.step s : CochainComplex B ℤ).X (s + (r : ℤ)))
    (ha : a ≫ (L.step s).arrow.f (s + (r : ℤ)) =
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).extendXIso
        ComplexShape.embeddingUpNat (by rfl)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (r : ℤ) s (s + (r : ℤ)) (by
            change (r : ℤ) + s = s + (r : ℤ)
            omega))) :
    ∃ e : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).X
        ((ComplexShape.up ℕ).prev r) ⟶ (L.gradedPiece s).X (s + (r : ℤ) - 1),
      Epi e ∧ e ≫ (L.gradedPiece s).d (s + (r : ℤ) - 1) (s + (r : ℤ)) =
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).d
          ((ComplexShape.up ℕ).prev r) r ≫ a ≫
          (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ)) := by sorry

end CategoryTheory.Functor
