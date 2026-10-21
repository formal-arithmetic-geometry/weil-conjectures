/-
Copyright (c) 2026 NP. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NP
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.CategoryTheory.FinitePostnikovIsomorphism
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# A heart test for bounded-below transformations

Source: main-20261015 blueprint, `sk-thm-properbasechange`, bounded below complexes paragraph;
Stacks Project, Derived Categories, Tags 08J5 and 05TC
(blueprint: lem-weil-pbc-heart-test-bounded-below).

## Main statements

- `DerivedCategory.Plus.heart_test_bounded_below`: invertibility on the cohomology objects
  in degree zero implies invertibility on a bounded-below object, with the degreewise
  truncation comparisons and their naturality formula.
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory.Plus

/-- A shift-compatible transformation of triangulated functors preserving every lower
cohomology bound is invertible at a bounded-below object if it is invertible on all its
cohomology objects placed in degree zero. The conclusion includes both truncation-map
isomorphisms, invertibility at the truncation, and the naturality formula in every degree.

Source: main-20261015 blueprint, `sk-thm-properbasechange`, bounded below complexes paragraph;
Stacks Project, Derived Categories, Tags 08J5 and 05TC
(blueprint: lem-weil-pbc-heart-test-bounded-below).

Proof:
1. For each m choose a lower bound a0 for E and put a = min(a0,m+1). Finite Postnikov
   propagation (`lem-weil-pbc-finite-postnikov-isomorphism`) gives invertibility at
   tau_{<=m} E, including the empty interval when m < a0.
2. The canonical truncation triangle (`lem-sf-derived-truncation-triangle`) has vertices
   tau_{<=m} E, E, and T_m = tau_{>=m+1} E. All lie in the full triangulated subcategory
   D+ (`def-weil-pbc-bounded-derived-subcategories`). Applying either triangulated functor
   gives a distinguished triangle (`def-weil-triangulated-category`).
3. Lower-bound preservation kills H^{m-1} and H^m of either functor's value on T_m.
   The long exact sequence (`lem-sf-derived-homology-long-exact`) makes both maps from
   H^m(F(tau_{<=m} E)) to H^m(F(E)) monic and epic, hence invertible.
4. Apply H^m to naturality at c_m and compose with the inverse of H^m(Phi(c_m)). This
   gives the displayed formula; all three factors are invertible by steps 1 and 3.
5. Thus H^m(eta_E) is invertible for every m. Cohomology detects isomorphisms in D+
   (`lem-weil-pbc-derived-plus-iso-on-cohomology`), so eta_E is invertible. No infinite
   limit or upper bound on E is used.
-/
theorem heart_test_bounded_below
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (Φ Ψ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [Φ.CommShift ℤ] [Ψ.CommShift ℤ] [Φ.IsTriangulated] [Ψ.IsTriangulated]
    (η : Φ ⟶ Ψ)
    (hη : ∀ M : DerivedCategory.Plus A,
      η.app (M⟦(1 : ℤ)⟧) ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app M =
        (Φ.commShiftIso (1 : ℤ)).hom.app M ≫ (η.app M)⟦(1 : ℤ)⟧')
    (hΦ : ∀ (M : DerivedCategory.Plus A) (n : ℤ),
      (∀ (q : ℤ), q < n → IsZero ((homologyFunctor A q).obj M)) →
        ∀ (q : ℤ), q < n → IsZero ((homologyFunctor B q).obj (Φ.obj M)))
    (hΨ : ∀ (M : DerivedCategory.Plus A) (n : ℤ),
      (∀ (q : ℤ), q < n → IsZero ((homologyFunctor A q).obj M)) →
        ∀ (q : ℤ), q < n → IsZero ((homologyFunctor B q).obj (Ψ.obj M)))
    (E : DerivedCategory.Plus A)
    (hH : ∀ (q : ℤ),
      IsIso (η.app ((singleFunctor A 0).obj ((homologyFunctor A q).obj E)))) :
    IsIso (η.app E) ∧ ∀ (m : ℤ),
      ∃ (hcΦ : IsIso ((homologyFunctor B m).map
          (Φ.map ((DerivedCategory.TStructure.t.onPlus.truncLEι m).app E)))),
        IsIso ((homologyFunctor B m).map
          (Ψ.map ((DerivedCategory.TStructure.t.onPlus.truncLEι m).app E))) ∧
        IsIso (η.app ((DerivedCategory.TStructure.t.onPlus.truncLE m).obj E)) ∧
        (homologyFunctor B m).map (η.app E) =
          @CategoryTheory.inv B _ _ _ ((homologyFunctor B m).map
            (Φ.map ((DerivedCategory.TStructure.t.onPlus.truncLEι m).app E))) hcΦ ≫
          (homologyFunctor B m).map
            (η.app ((DerivedCategory.TStructure.t.onPlus.truncLE m).obj E)) ≫
          (homologyFunctor B m).map
            (Ψ.map ((DerivedCategory.TStructure.t.onPlus.truncLEι m).app E)) := by
  sorry

end DerivedCategory.Plus
