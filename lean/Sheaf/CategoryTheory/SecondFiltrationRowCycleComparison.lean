/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
import Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries

/-! # The normalized row-cycle comparison with the first quotient page

Source: Stacks Project, Homology, Tag 0130, clauses 2 and 4, and Tag 012K.
(blueprint: lem-sp-second-filtration-row-cycle-comparison).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The diagonal inclusion of a mapped row term, using the canonical extension
isomorphism before its total coprojection. This is a concrete map, independent
of page differentials or choices of quotient comparisons.
Source: Stacks Project, Tag 0130, the second-filtration graded identification.
(blueprint: lem-sp-second-filtration-row-cycle-comparison). -/
noncomputable def secondFiltrationRowι
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (r : ℕ) (s : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).X r ⟶
      (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip.total
        (ComplexShape.up ℤ)).X (s + (r : ℤ)) :=
  (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).extendXIso
    ComplexShape.embeddingUpNat (by rfl)).inv ≫
    (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).ιTotal
      (ComplexShape.up ℤ) (r : ℤ) s (s + (r : ℤ)) (by
        change (r : ℤ) + s = s + (r : ℤ)
        omega)

/-- Row cycles have canonical lifts to the filtration and graded cycles. Their
quotient is row homology, normalized by the row homology projection. No page
*differential* occurs in this statement.
Source: Stacks Project, Tag 0130, clauses 2 and 4; Tag 012K, the first-page
cycle/boundary formulas.
(blueprint: lem-sp-second-filtration-row-cycle-comparison).

Proof. Write J for the flipped mapped extended bicomplex. Lift its diagonal
inclusion through L^s in degree s+r. The equality of subobjects hL and membership
of s in the interval [s,s+r] give the unique lift through the monomorphism.
The projection onto the (r,s) summand kills every summand of L^(s+1); it descends
to the graded quotient and is inverse to the diagonal lift followed by the
graded projection. Check both identities on the diagonal coprojections.
On the graded quotient the complex-coordinate differential disappears and the
resolution differential remains. Thus this graded comparison identifies the
row cycles and boundaries with its kernel and image. Apply the first-page
cycles-boundaries identities to obtain the same subobjects as complexCycles
and complexBoundaries. Restrict the lifted diagonal map to row cycles to get t,
and factor its graded class through the identified cycle subobject to get x.
The cokernel of the boundary inclusion is row homology; its universal property
gives e with x followed by the page projection and e.hom equal to homologyπ.
Its inverse is obtained from the inverse graded comparison, so e is an iso.
Extension by zero preserves this calculation at all natural degrees: for r=0
both incoming boundary images are zero. The normalizations determine t and x
by monicity and e by the epic projection from row cycles. This remains valid
for negative s, since the interval is [s,s+r], not [0,s+r]. -/
theorem secondFiltration_row_cycle_comparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p) :
    let K := (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
      (ComplexShape.up ℤ)
    let R := fun s : ℤ ↦ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)
    ∃ (e : ∀ (r : ℕ) (s : ℤ), filteredComplexPageObject K L 1 (s, (r : ℤ)) ≅
        (R s).homology r)
      (t : ∀ (r : ℕ) (s : ℤ), (R s).cycles r ⟶
        (L.step s : CochainComplex B ℤ).X (s + (r : ℤ)))
      (x : ∀ (r : ℕ) (s : ℤ), (R s).cycles r ⟶
        (L.complexCycles s (s + (r : ℤ)) 1 : B)),
      (∀ r s, t r s ≫ (L.step s).arrow.f (s + (r : ℤ)) =
        (R s).iCycles r ≫ secondFiltrationRowι F I r s) ∧
      (∀ r s, x r s ≫ (L.complexCycles s (s + (r : ℤ)) 1).arrow =
        t r s ≫ (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ))) ∧
      (∀ r s, x r s ≫ filteredComplexPageπ K L 1 (s, (r : ℤ)) ≫ (e r s).hom =
        (R s).homologyπ r) := by sorry

end CategoryTheory.Functor
