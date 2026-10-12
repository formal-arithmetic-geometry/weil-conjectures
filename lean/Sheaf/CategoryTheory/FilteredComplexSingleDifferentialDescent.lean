/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.FilteredComplexBoundariesLECycles

/-!
# Descent of one filtered differential through the cycle-boundary quotients

Source: Stacks Project, Homology, Tag 012K, displayed differential formula.
(blueprint: lem-sp-filtered-complex-single-differential-descent).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The underlying complex differential descends between the two actual cokernels
in one related pair of bidegrees. No square-zero or uniqueness assertion is included.
Source: Stacks Project, Tag 012K, displayed differential formula.
(blueprint: lem-sp-filtered-complex-single-differential-descent).

Proof. Write p = i.1, n = i.1+i.2; relatedness gives j = (p+r,i.2+1-r).
Restrict d to R = F^p K^n intersect d-inverse(F^(p+r) K^(n+1)). Its
image lies in the target cycle representatives because d squared = 0.
Project this image to the target graded cycles and then to their cokernel
by target boundaries. The projection R to source graded cycles is epic;
its kernel is R intersect F^(p+1). Differentiating this intersection gives
a target boundary: the incoming filtration degree of the target boundary
is (p+r)-r+1 = p+1. Hence the composite kills that kernel and factors
through source graded cycles by the cokernel universal property in an
abelian category. Its restriction to source boundaries is zero: after
an epimorphic pullback, a boundary representative is an incoming
differential plus an element of F^(p+1), and both summands have zero image
in the target quotient, the first by d squared = 0 and the second by the
previous calculation. Descend once more through the source boundary
cokernel. For arbitrary t,t',x,y in the statement, t factors through R
by the pullback universal property; the two descent equations and the
monicity of the target filtration inclusion and cycle inclusion give
exactly the asserted representative equation. All descent is performed
with finite limits, images and cokernels. -/
theorem filteredComplex_single_differential_descent
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (i j : ℤ × ℤ) (hij : (ComplexShape.up' (r, 1 - r)).Rel i j) :
    let Q := fun pq : ℤ × ℤ ↦ cokernel (Subobject.ofLE _ _
      (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) r))
    let π := fun pq : ℤ × ℤ ↦ cokernel.π (Subobject.ofLE _ _
      (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) r))
    ∃ δ : Q i ⟶ Q j,
      ∀ (A : C)
        (t : A ⟶ (F.step i.1 : CochainComplex C ℤ).X (i.1 + i.2))
        (t' : A ⟶ (F.step j.1 : CochainComplex C ℤ).X (j.1 + j.2))
        (x : A ⟶ (F.complexCycles i.1 (i.1 + i.2) r : C))
        (y : A ⟶ (F.complexCycles j.1 (j.1 + j.2) r : C)),
        t ≫ (F.step i.1).arrow.f (i.1 + i.2) ≫ K.d (i.1 + i.2) (j.1 + j.2) =
          t' ≫ (F.step j.1).arrow.f (j.1 + j.2) →
        x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow =
          t ≫ (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2) →
        y ≫ (F.complexCycles j.1 (j.1 + j.2) r).arrow =
          t' ≫ (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2) →
        x ≫ π i ≫ δ = y ≫ π j := by sorry

end CategoryTheory
