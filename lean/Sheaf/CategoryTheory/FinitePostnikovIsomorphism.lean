/-
Copyright (c) 2026 Q12. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q12
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Invertibility along a finite Postnikov filtration

Source: Stacks Project, Derived Categories, Remark 08J5, and the bounded below complexes
paragraph of the main-20261015 blueprint, unit `sk-thm-properbasechange`
(blueprint: lem-weil-pbc-finite-postnikov-isomorphism).

## Main statements

- `DerivedCategory.Plus.isIso_app_truncLE_of_isIso_app_homology`: a shift-compatible natural
  transformation of triangulated functors is invertible on an upper truncation if it is
  invertible on the finitely many contributing cohomology objects placed in degree zero.
-/

@[expose] public section

universe w v u vT uT

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory.Plus

/-- Finite Postnikov propagation of invertibility, including the empty interval `b = a - 1`.

Source: Stacks Project, Derived Categories, Remark 08J5, and the bounded below complexes
paragraph of the main-20261015 blueprint, unit `sk-thm-properbasechange`
(blueprint: lem-weil-pbc-finite-postnikov-isomorphism).

Proof:
1. Put E_q = tau_{<=q} E. Truncation cohomology
   (`lem-weil-pbc-truncation-cohomology`) shows that E_q is bounded below, with cohomology
   in [a,q]. The objects C_q = H^q(E)[0][-q] are bounded below as well. The full subcategory
   D+ inherits the triangulated structure (`def-weil-pbc-bounded-derived-subcategories`).
2. E_{a-1} has zero cohomology in every degree, so it is zero by cohomology detection
   (`lem-weil-pbc-derived-plus-iso-on-cohomology`). The exact functors are additive
   (`def-weil-triangulated-category`); their values on E_{a-1} are zero objects. Hence the
   zero map is an inverse to the component of eta at E_{a-1}.
3. The displayed shift equation conjugates eta at M[1] to the shift of eta at M. Iteration
   forwards and backwards gives invertibility at all integral shifts. Naturality transports
   invertibility along isomorphisms. Thus the hypothesis on H^q(E)[0] gives invertibility
   at C_q for a <= q <= b (`def-weil-triangulated-category`).
4. For a <= q <= b apply both functors to the successive distinguished triangle
   E_{q-1} -> E_q -> C_q -> E_{q-1}[1] (`lem-weil-pbc-truncation-triangle`). The shift
   equation makes the components of eta a triangle morphism. Two-out-of-three
   (`lem-sf-triangle-two-out-of-three`) propagates invertibility from E_{q-1} and C_q to E_q.
5. Starting at q = a-1, perform b-a+1 induction steps. The result is invertibility at
   tau_{<=b} E. When b = a-1, the interval hypothesis is vacuous and step 2 gives the result.
-/
theorem isIso_app_truncLE_of_isIso_app_homology
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {T : Type uT} [Category.{vT} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
    [∀ (n : ℤ), (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
    (Φ Ψ : DerivedCategory.Plus A ⥤ T) [Φ.CommShift ℤ] [Ψ.CommShift ℤ]
    [Φ.IsTriangulated] [Ψ.IsTriangulated] (η : Φ ⟶ Ψ)
    (hη : ∀ M : DerivedCategory.Plus A,
      η.app (M⟦(1 : ℤ)⟧) ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app M =
        (Φ.commShiftIso (1 : ℤ)).hom.app M ≫ (η.app M)⟦(1 : ℤ)⟧')
    (E : DerivedCategory.Plus A) (a b : ℤ) (hab : a - 1 ≤ b)
    (hE : ∀ (q : ℤ), q < a → IsZero ((homologyFunctor A q).obj E))
    (hH : ∀ (q : ℤ), a ≤ q → q ≤ b →
      IsIso (η.app ((singleFunctor A 0).obj ((homologyFunctor A q).obj E)))) :
    IsIso (η.app ((DerivedCategory.TStructure.t.onPlus.truncLE b).obj E)) := by
  sorry

end DerivedCategory.Plus
