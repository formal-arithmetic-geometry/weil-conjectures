/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste

/-! # Componentwise composition of adjunction mates -/

@[expose] public section
set_option autoImplicit false
namespace CategoryTheory

private theorem conjugate_triangle
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {P : B ⥤ A} {R : A ⥤ B} {Q : D ⥤ B} {S : B ⥤ D}
    {H : E ⥤ D} {G : D ⥤ E} {T : D ⥤ A} {V : A ⥤ D}
    {F : E ⥤ A} {Rf : A ⥤ E} {K : E ⥤ B} {Rk : B ⥤ E}
    (ap : P ⊣ R) (aq : Q ⊣ S) (ah : H ⊣ G) (ac : T ⊣ V)
    (af : F ⊣ Rf) (ak : K ⊣ Rk)
    (α : F ⟶ K ⋙ P) (β : K ⟶ H ⋙ Q) (gamma : F ⟶ H ⋙ T) (τ : T ⟶ Q ⋙ P)
    (hc : α ≫ Functor.whiskerRight β P = gamma ≫ Functor.whiskerLeft H τ) :
    Functor.whiskerRight (conjugateEquiv (aq.comp ap) ac τ) G ≫
        conjugateEquiv (ah.comp ac) af gamma =
      Functor.whiskerLeft R (conjugateEquiv (ah.comp aq) ak β) ≫
        conjugateEquiv (ak.comp ap) af α := by
  rw [← conjugateEquiv_whiskerLeft (aq.comp ap) ac ah τ,
    conjugateEquiv_comp (ah.comp (aq.comp ap)) (ah.comp ac) af]
  rw [← Adjunction.comp_assoc, ← hc]
  have hh := conjugateEquiv_comp ((ah.comp aq).comp ap) (ak.comp ap) af
    (Functor.whiskerRight β P) α
  rw [conjugateEquiv_whiskerRight (ah.comp aq) ak ap β] at hh
  exact hh.symm

/-- The componentwise composition law for four compatible adjunction mates.

Source: blueprint Steps 15--16 of the compact-support condensed realization
(blueprint: lem-pur-conjugate-composition-components).

Proof: apply the conjugate equivalence to the assumed commuting square.
Conjugation reverses composition and carries the two whiskerings to the
opposite whiskerings. Associativity of composed adjunctions identifies the
middle adjunctions. Substitute the four specified mates and evaluate at the
object. -/
theorem conjugateComposition_app
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {P : B ⥤ A} {R : A ⥤ B} {Q : D ⥤ B} {S : B ⥤ D}
    {H : E ⥤ D} {G : D ⥤ E} {T : D ⥤ A} {V : A ⥤ D}
    {F : E ⥤ A} {Rf : A ⥤ E} {K : E ⥤ B} {Rk : B ⥤ E}
    (ap : P ⊣ R) (aq : Q ⊣ S) (ah : H ⊣ G) (ac : T ⊣ V)
    (af : F ⊣ Rf) (ak : K ⊣ Rk)
    (α : F ⟶ K ⋙ P) (β : K ⟶ H ⋙ Q) (gamma : F ⟶ H ⋙ T) (τ : T ⟶ Q ⋙ P)
    (hc : ∀ N, α.app N ≫ P.map (β.app N) =
      gamma.app N ≫ τ.app (H.obj N))
    (t : R ⋙ S ⟶ V) (a : R ⋙ Rk ⟶ Rf) (b : S ⋙ G ⟶ Rk) (c : V ⋙ G ⟶ Rf)
    (ht : conjugateEquiv (aq.comp ap) ac τ = t)
    (ha : conjugateEquiv (ak.comp ap) af α = a)
    (hb : conjugateEquiv (ah.comp aq) ak β = b)
    (hg : conjugateEquiv (ah.comp ac) af gamma = c) (M : A) :
    @Eq (G.obj (S.obj (R.obj M)) ⟶ Rf.obj M)
      (G.map (t.app M) ≫ c.app M) (b.app (R.obj M) ≫ a.app M) := by
  have hsq : α ≫ Functor.whiskerRight β P =
      gamma ≫ Functor.whiskerLeft H τ := by
    ext N
    exact hc N
  have h := conjugate_triangle ap aq ah ac af ak α β gamma τ hsq
  rw [ht, ha, hb, hg] at h
  exact NatTrans.congr_app h M

end CategoryTheory
