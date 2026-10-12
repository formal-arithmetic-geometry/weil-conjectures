/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredComplexSpectralSequence
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.DoubleComplexTotal

/-! # Signed row identifications for the second-filtration spectral sequence

Source: Stacks Project, Tag 0130; blueprint thm-sp-if-e1, proof paragraph 1.
(blueprint: lem-sp-second-filtration-row-cohomology).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Row cohomology, including the differential, for the second-degree filtration.
The differential retains the totalization sign. No injectivity or augmentation
is assumed, and no convergence is claimed.
Source: Stacks Project, Tag 0130; blueprint thm-sp-if-e1, proof paragraph 1.
(blueprint: lem-sp-second-filtration-row-cohomology).

Proof.
Build the spectral sequence of the filtration by the differential-object self-map
construction, retaining the page-zero and cycle/boundary identifications. The graded
complex at s is the row F(I.X s), extended by zero and placed in degrees s+r: the
component raising s disappears on taking the quotient. Thus page one is its cohomology.
To compute d₁, lift a row cocycle to L^s/L^(s+2). Its total differential has only
the component raising complex degree, with coefficient (-1)^r. The connecting map
is consequently (-1)^r times the map of row cohomology induced by I.d s (s+1).
The extended row is zero in negative resolution degrees, so its cohomology there
vanishes. This proves the negative-degree page-one clause. -/
theorem secondFiltration_row_cohomology
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
    ∃ (E : CohomologicalSpectralSequence B 0)
      (e₀ : ∀ p q : ℤ, (E.page 0).X (p, q) ≅ (L.gradedPiece p).X (p + q))
      (e₁ : ∀ (r : ℕ) (s : ℤ), (E.page 1).X (s, (r : ℤ)) ≅
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).homology r),
      (∀ p q : ℤ, (E.page 0).d (p, q) (p, q + 1) ≫ (e₀ p (q + 1)).hom =
        (e₀ p q).hom ≫ (L.gradedPiece p).d (p + q) (p + (q + 1))) ∧
      (∀ (p q t : ℤ) (ht : 1 ≤ t),
        ∃ hBZ : L.complexBoundaries p (p + q) t ≤ L.complexCycles p (p + q) t,
          Nonempty ((E.page t (le_trans (by decide : (0 : ℤ) ≤ 1) ht)).X (p, q) ≅
            cokernel (Subobject.ofLE _ _ hBZ))) ∧
      (∀ (r : ℕ) (s : ℤ),
        (E.page 1).d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫ (e₁ r (s + 1)).hom =
          (r : ℤ).negOnePow • ((e₁ r s).hom ≫ HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.d s (s + 1))) r)) ∧
      (∀ p q : ℤ, q < 0 → IsZero ((E.page 1).X (p, q))) := by sorry

end CategoryTheory.Functor
