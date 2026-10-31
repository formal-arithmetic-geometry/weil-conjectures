/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-!
# Localized derived adjunction from a resolving class

This file records the statement corresponding to Stacks Project, Tags 06XN,
05SE, 05SU and 0FND.  It is the arbitrary triangulated-category form used by
the six-functors construction.  The proof is postponed: the resolving-class
hypotheses give essential constancy of the denominator diagrams, hence a
pointwise and universal left derived functor.  The induced right functor is an
absolute right derived functor by the localization universal property.  The
absolute-derived-adjunction theorem then supplies the adjunction; its unit and
counit are normalized by the displayed equations.  Shift compatibility is
transported through the same universal properties, with coherence forced by
uniqueness.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe uK vK uH vH uA vA uB vB

namespace CategoryTheory

/-- Stacks Project, Tags 06XN, 05SE, 05SU and 0FND (blueprint: lem-sf-localized-derived-adjunction).

Let `K` and `H` be triangulated categories, with saturated multiplicative
systems `W` and `V` compatible with their triangulations.  Let `Q` and `Q'`
be triangulated localization functors.  For an exact adjunction `E ⊣ R`,
assume that `R` carries `V`-arrows to `W`-arrows, and fix the induced-functor
comparison `β : R ⋙ Q ≅ Q' ⋙ Rbar`.  If `P` resolves every object of `K`
and `E` sends `W`-arrows between `P`-objects to isomorphisms, then the
localized left functor has an everywhere-defined pointwise and universal left
derived functor.  Its comparison is invertible on `P`, it is adjoint to
`Rbar`, and the unit and counit satisfy the normalized equations below.
All derived functors, comparisons, and the adjunction commute with integer
shifts; the shift structure `hRbar` on `Rbar` is the one induced from that of
`R ⋙ Q` through `β` (the conjunct making `β` shift-compatible pins it), so the
adjunction is compatible with the canonical shift of `Rbar` and not merely
with the one `Adjunction.commShift_of_leftAdjoint` would supply for any `L`.
No ordinary-complex realization is assumed.

Proof (blueprint steps; postponed):
1. `W` has a right calculus of fractions and two-out-of-three (MS1–MS4).  The
   resolving-class lemma (Tag 06XN) makes every denominator diagram
   `W/X → B` of `F = E ⋙ Q'` essentially constant, with cone `u_s`, and
   `u_{id_X}` is invertible for `X ∈ P`.
2. The pointwise-Kan bridge identifies these values with the pointwise right
   Kan extension of `F` along `Q`; total-left-derived assembly gives `L` and
   `c : Q ⋙ L ⟶ F`, universal (Tags 05S9, 05SE), with `c_X = u_{id_X}`.
3. `(L, c)` is absolute: any functor applied to the cone/retraction equations
   of essential constancy keeps them, and right fractions force the cone.
4. `(Rbar, β)` is an absolute right derived pair, because precomposition with
   `Q'` is fully faithful on natural transformations.
5. The absolute-derived-adjunction theorem (Tag 0FND) gives `L ⊣ Rbar`.
6. The unit is the unique lift of `Q(u)` through the universal property of
   `(Rbar ⋙ L, Rbar c)`; the counit descends `Q'(v_Y) ∘ c_{RY}` along `Q'`.
7. Both triangle identities hold for these normalized maps, by universality
   of `c` and full faithfulness of precomposition with `Q'`.
8. The shift on `L` is the comparison of `(L, c)` with its conjugate by the
   shifts; uniqueness gives the zero/addition coherences and the compatibility
   of `c` (Tag 05SU).
9. The shift on `Rbar` is induced from `R ⋙ Q` through `β`.  The unit is
   compatible by universality, and hence the counit is compatible too
   (adjunction-shift uniqueness).
-/
theorem exists_localizedDerivedAdjunction
    {K : Type uK} [Category.{vK} K] [HasZeroObject K] [HasShift K ℤ]
    [Preadditive K] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K] [IsTriangulated K]
    {H : Type uH} [Category.{vH} H] [HasZeroObject H] [HasShift H ℤ]
    [Preadditive H] [∀ n : ℤ, (shiftFunctor H n).Additive]
    [Pretriangulated H] [IsTriangulated H]
    {A : Type uA} [Category.{vA} A] [HasZeroObject A] [HasShift A ℤ]
    [Preadditive A] [∀ n : ℤ, (shiftFunctor A n).Additive]
    [Pretriangulated A] [IsTriangulated A]
    {B : Type uB} [Category.{vB} B] [HasZeroObject B] [HasShift B ℤ]
    [Preadditive B] [∀ n : ℤ, (shiftFunctor B n).Additive]
    [Pretriangulated B] [IsTriangulated B]
    (W : MorphismProperty K) (V : MorphismProperty H)
    (hW : W.IsSaturatedTriangulatedMultiplicativeSystem)
    (hV : V.IsSaturatedTriangulatedMultiplicativeSystem)
    (Q : K ⥤ A) (Q' : H ⥤ B)
    [Q.IsLocalization W] [Q'.IsLocalization V]
    [Q.CommShift ℤ] [Q'.CommShift ℤ]
    [Q.IsTriangulated] [Q'.IsTriangulated]
    (E : K ⥤ H) (R : H ⥤ K)
    [E.CommShift ℤ] [R.CommShift ℤ]
    [E.IsTriangulated] [R.IsTriangulated]
    (adj : E ⊣ R) [adj.CommShift ℤ]
    (hRV : ∀ {X Y : H} (f : X ⟶ Y), V f → W (R.map f))
    (Rbar : B ⥤ A)
    (β : R ⋙ Q ≅ Q' ⋙ Rbar)
    (P : Set K)
    (hres : ∀ X : K, ∃ (P' : K) (p : P' ⟶ X), P P' ∧ W p)
    (hinv : ∀ {X Y : K} (s : X ⟶ Y), P X → P Y → W s →
      IsIso ((E ⋙ Q').map s)) :
    ∃ (L : A ⥤ B) (c : Q ⋙ L ⟶ E ⋙ Q')
      (hL : L.CommShift ℤ) (hRbar : Rbar.CommShift ℤ) (d : L ⊣ Rbar),
      Functor.HasPointwiseLeftDerivedFunctor (E ⋙ Q') W ∧
      L.IsLeftDerivedFunctor c W ∧
      (∀ X : K, P X → IsIso (c.app X)) ∧
      @NatTrans.CommShift _ _ _ _ (Q ⋙ L) (E ⋙ Q') c ℤ
        inferInstance inferInstance inferInstance
        (@Functor.CommShift.comp _ _ _ _ _ _ Q L ℤ
          inferInstance inferInstance inferInstance inferInstance
          (inferInstance : Q.CommShift ℤ) hL)
        (@Functor.CommShift.comp _ _ _ _ _ _ E Q' ℤ
          inferInstance inferInstance inferInstance inferInstance
          (inferInstance : E.CommShift ℤ) (inferInstance : Q'.CommShift ℤ)) ∧
      @Adjunction.CommShift A B _ _ L Rbar d ℤ
        inferInstance inferInstance inferInstance hL hRbar ∧
      @NatTrans.CommShift _ _ _ _ (R ⋙ Q) (Q' ⋙ Rbar) β.hom ℤ
        inferInstance inferInstance inferInstance
        (@Functor.CommShift.comp _ _ _ _ _ _ R Q ℤ
          inferInstance inferInstance inferInstance inferInstance
          (inferInstance : R.CommShift ℤ) (inferInstance : Q.CommShift ℤ))
        (@Functor.CommShift.comp _ _ _ _ _ _ Q' Rbar ℤ
          inferInstance inferInstance inferInstance inferInstance
          (inferInstance : Q'.CommShift ℤ) hRbar) ∧
      (∀ X : K,
        d.unit.app (Q.obj X) ≫ Rbar.map (c.app X) =
          Q.map (adj.unit.app X) ≫ β.hom.app (E.obj X)) ∧
      (∀ Y : H,
        L.map (β.hom.app Y) ≫ d.counit.app (Q'.obj Y) =
          c.app (R.obj Y) ≫ Q'.map (adj.counit.app Y)) := by
  sorry

end CategoryTheory
