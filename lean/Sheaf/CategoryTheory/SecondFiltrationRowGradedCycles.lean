/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients

/-! # Row cycles in the second graded filtration

Source: Stacks Project, Homology, Tags 0130 and 012K.
(blueprint: lem-sp-second-filtration-row-graded-cycles).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The normalized diagonal map induces an isomorphism on cycles, before taking
any quotient by boundaries.
Source: Stacks Project, Tag 0130, clause 2; Tag 012K, first-page cycle formula.
(blueprint: lem-sp-second-filtration-row-graded-cycles).

Proof. Write J = flip(mappedFunctor F(I)) and n = s+r. In degree n the second
step is the finite sum of the images of the diagonal inclusions with second
coordinate in [s,n]. Project the total coproduct onto its (r,s) summand, then
apply the extension isomorphism to recover the mapped row term. This projection
kills every summand of the next step, whose second coordinate is at least s+1.
It therefore descends to the graded quotient. Conversely lift the (r,s) summand
through the step and project to the quotient. On all generating inclusions these
two morphisms are inverse: the summand s gives identity, and all other summands
are killed in the quotient. This proves the degreewise graded comparison.
The total differential of the diagonal inclusion is the resolution differential
plus the signed differential raising s. The latter factors through the next
step and disappears in the quotient. Thus the comparison intertwines the row
differential with the graded differential. Apply the universal property of the
kernels of these outgoing differentials to obtain a mutually inverse pair of
cycle maps. The first-page cycle formula identifies the graded kernel with
L.complexCycles s n 1. Monicity of the filtration inclusion forces the given t
to equal the restriction of the term lift, so the asserted normalization follows.
This uses [s,n], never s>=0. At r=0 the interval contains just s; no incoming
term or boundary calculation is used. Zero rows give the unique zero-object iso.
-/
theorem secondFiltration_row_graded_cycles
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
    (r : ℕ) (s : ℤ)
    (t : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).cycles r ⟶
      (L.step s : CochainComplex B ℤ).X (s + (r : ℤ)))
    (ht : t ≫ (L.step s).arrow.f (s + (r : ℤ)) =
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).iCycles r ≫
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).extendXIso
        ComplexShape.embeddingUpNat (by rfl)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (r : ℤ) s (s + (r : ℤ)) (by
            change (r : ℤ) + s = s + (r : ℤ)
            omega))) :
    ∃ c : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).cycles r ≅
        (L.complexCycles s (s + (r : ℤ)) 1 : B),
      c.hom ≫ (L.complexCycles s (s + (r : ℤ)) 1).arrow =
        t ≫ (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ)) := by sorry

end CategoryTheory.Functor
