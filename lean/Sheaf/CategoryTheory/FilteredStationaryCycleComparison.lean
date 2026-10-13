/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Sheaf.CategoryTheory.FilteredStableSubquotient

/-! # A stationary quotient comparison characterized on actual cycles

Source: Stacks Project, Homology, Tags 012K, 012Q and 012W.
(blueprint: lem-weil-pbc-stationary-cycle-comparison).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- At stationary outer bounds, actual cycles cover the graded cycles, and their
homology classes determine the stationary comparison.
Source: Stacks Project, Homology, Tags 012K, 012Q and 012W.
(blueprint: lem-weil-pbc-stationary-cycle-comparison).

Proof. Write n=q+p. The upper bound makes the r-cycle condition d(x)=0.
Thus projecting the cycles of F^q K to gr^q K has image exactly the graded
r-cycles; adding F^(q+1) before taking the graded projection does not change
its image. Factor this projection through its image to obtain the epimorphism z.
The lower bound makes r-boundaries the graded images of total boundaries
lying in F^q K. The map from cycles of F^q K to H^n(K), transported by c,
has image H.step q, by the epic factorization a q and its inclusion equation.
Its kernel is the total boundaries lying in F^q K. Quotienting this image by
H.step (q+1) therefore kills precisely those boundaries and the cycles of
F^(q+1) K. The two cokernel presentations have the same kernel on the actual
cycles, so their universal properties give mutually inverse comparison maps.
The resulting isomorphism satisfies the displayed equation. The inclusion
of graded cycles is monic, so the representative equation uniquely fixes z;
since z and the page projection are epic, the last equation uniquely fixes
the comparison. This also covers zero complexes and zero graded pieces. -/
theorem filteredStationary_cycle_comparison
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (q p r : ℤ) (hr : 1 ≤ r)
    (hupper : F.complexStep (q + r) (q + p + 1) = ⊥)
    (hlower : F.complexStep (q - r + 1) (q + p - 1) = ⊤)
    {Y : C} (c : K.homology (q + p) ≅ Y) (H : DecreasingFiltration Y)
    (a : ∀ i : ℤ, (F.step i : CochainComplex C ℤ).homology (q + p) ⟶ (H.step i : C))
    (ha : ∀ i : ℤ, a i ≫ (H.step i).arrow =
      HomologicalComplex.homologyMap (F.step i).arrow (q + p) ≫ c.hom)
    (hepi : ∀ i : ℤ, Epi (a i)) :
    ∃ (z : (F.step q : CochainComplex C ℤ).cycles (q + p) ⟶
        (F.complexCycles q (q + p) r : C))
      (e : filteredComplexPageObject K F r (q, p) ≅ H.gradedPiece q),
      Epi z ∧
      z ≫ (F.complexCycles q (q + p) r).arrow =
        (F.step q : CochainComplex C ℤ).iCycles (q + p) ≫
          (F.complexQuotientπ q (q + 1) (by omega)).f (q + p) ∧
      z ≫ filteredComplexPageπ K F r (q, p) ≫ e.hom =
        (F.step q : CochainComplex C ℤ).homologyπ (q + p) ≫ a q ≫
          cokernel.π (Subobject.ofLE (H.step (q + 1)) (H.step q)
            (H.antitone_step (Int.le_add_one (le_refl q)))) := by sorry

end CategoryTheory
