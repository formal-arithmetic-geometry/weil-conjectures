/-
Copyright (c) 2026 Q12. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q12
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
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
  let t := DerivedCategory.Plus.TStructure.t (C := A)
  have hshift (M : DerivedCategory.Plus A) :
      IsIso (η.app (M⟦(1 : ℤ)⟧)) ↔ IsIso (η.app M) := by
    have heq : η.app (M⟦(1 : ℤ)⟧) = (Φ.commShiftIso (1 : ℤ)).hom.app M ≫
        (η.app M)⟦(1 : ℤ)⟧' ≫ (Ψ.commShiftIso (1 : ℤ)).inv.app M := by
      rw [← cancel_mono ((Ψ.commShiftIso (1 : ℤ)).hom.app M)]
      simpa using hη M
    rw [heq, isIso_comp_left_iff, isIso_comp_right_iff]
    exact ⟨fun _ ↦ isIso_of_reflects_iso (η.app M) (shiftFunctor T (1 : ℤ)),
      fun _ ↦ inferInstance⟩
  have hshifts (M : DerivedCategory.Plus A) (n : ℤ) (hM : IsIso (η.app M)) :
      IsIso (η.app (M⟦n⟧)) := by
    induction n using Int.inductionOn' (b := 0) with
    | zero =>
      exact (NatTrans.isIso_app_iff_of_iso η
        ((shiftFunctorZero (DerivedCategory.Plus A) ℤ).app M)).2 hM
    | succ n _ ih =>
      exact (NatTrans.isIso_app_iff_of_iso η
        ((shiftFunctorAdd (DerivedCategory.Plus A) n 1).app M)).2 ((hshift _).2 ih)
    | pred n _ ih =>
      apply (hshift _).1
      exact (NatTrans.isIso_app_iff_of_iso η
        ((shiftFunctorAdd' (DerivedCategory.Plus A) (n - 1) 1 n (by omega)).app M)).1 ih
  have : E.IsGE a := (isGE_ι_obj_iff E a).1
    ((DerivedCategory.isGE_iff (ι.obj E) a).2 hE)
  have hmain (q : ℤ) (hq : a - 1 ≤ q) :
      q ≤ b → IsIso (η.app ((t.truncLE q).obj E)) := by
    induction q, hq using Int.leInduction with
    | base =>
      intro _
      have hz := t.isZero_truncLE_obj_of_isGE (a - 1) a (by omega) E
      exact (Φ.map_isZero hz).isIso (Ψ.map_isZero hz) _
    | succ q hq ih =>
      intro hqb
      let X := (t.truncLE (q + 1)).obj E
      let Δ := (t.triangleLEGE q (q + 1) rfl).obj X
      have hi := ih (by omega)
      have := t.isIso_truncLE_map_truncLEι_app q (q + 1) (by omega) E
      have h₁ : IsIso (η.app Δ.obj₁) :=
        (NatTrans.isIso_app_iff_of_iso η
          (asIso ((t.truncLE q).map ((t.truncLEι (q + 1)).app E)))).2 hi
      have h₃ : IsIso (η.app Δ.obj₃) := by
        obtain ⟨e⟩ := nonempty_eTruncGE_eTruncLT_iso_singleFunctor E (q + 1)
        apply (NatTrans.isIso_app_iff_of_iso η e).2
        apply (NatTrans.isIso_app_iff_of_iso η
          (((singleFunctors A).shiftIso (-(q + 1)) (q + 1) 0 (by omega)).app
            ((homologyFunctor A (q + 1)).obj E))).1
        exact hshifts _ _ (hH (q + 1) (by omega) hqb)
      let γ : Φ.mapTriangle.obj Δ ⟶ Ψ.mapTriangle.obj Δ :=
        Pretriangulated.Triangle.homMk _ _ (η.app _) (η.app _) (η.app _)
          (by simp) (by simp) (by
            dsimp
            simp only [Category.assoc, ← hη, NatTrans.naturality_assoc])
      exact Pretriangulated.isIso₂_of_isIso₁₃ γ
        (Φ.map_distinguished _ (t.triangleLEGE_distinguished q (q + 1) rfl X))
        (Ψ.map_distinguished _ (t.triangleLEGE_distinguished q (q + 1) rfl X)) h₁ h₃
  exact hmain b hab le_rfl

end DerivedCategory.Plus
