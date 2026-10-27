/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.CategoryTheory.Localization.Predicate
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-!
# Transport of localized universal left derived pairs

Source: Stacks Project, Categories, Tags 04VG and 04VK; Derived Categories, Tag 05S9
and equation-everywhere. The simultaneous transport is an ordinary-category calculation
using those conventions (blueprint: lem-trf-localized-universal-derived-pair-transport).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC uC' vC' uD vD uD' vD' uH vH uH' vH'

namespace CategoryTheory

/-- Equivalences preserving the specified morphism classes descend to localizations and
transport universal left derived pairs, including their counits and universal bijections.
Source: Stacks Project, Categories, Tags 04VG and 04VK; Derived Categories, Tag 05S9
and equation-everywhere (blueprint: lem-trf-localized-universal-derived-pair-transport).

Write `d = D.functor`, `j = D.inverse`, `t = T.functor`, `u = T.inverse`.
The equations for `D.unitIso` and `D.counitIso`, and their uniqueness clauses, specify
precisely their localized lifts relative to `a,b`. The triangle identities belong to
`D : Lcat ≌ Lcat'`. The transported functor is literally `j ⋙ L ⋙ t`.
The equivalences `B,M,P.symm` below are the three displayed natural-transformation
bijections; their component formulas fix the equivalence conjugations and the middle
universal-counit map. The final equality identifies their composite with the new counit.

Proof:
1. Since `e.functor ⋙ Q'` inverts `W` and `e.inverse ⋙ Q` inverts `W'`, lift them
through `Q,Q'` using `lem-weil-pbc-localization-universal-property`, obtaining `d,j,a,b`.
2. In Lean's left-to-right composition convention set `c = j(a) ≫ b_e` and
`f = d(b) ≫ a_i`. Lift `Q(eta) ≫ c.inv` to the unit `U`, and `f ≫ Q'(theta)`
to the counit `V`. The component equations below specify these lifts.
Localization lifts inverses and detects equality, proving uniqueness of both lifts.
3. Check the two triangles after precomposition with `Q,Q'`. Naturality of `V` at `a`
and of `U` at `b` reduces their conjugated components to
`Q'(e(eta) ≫ theta_e)` and `Q(eta_i ≫ i(theta))`, respectively. The original triangles
make these identities, and localization detects the two natural-transformation equalities.
4. Define `B(alpha)` by applying `u` to `alpha_d`, then to `tL(U.inv)`, and composing
with the inverse target unit. Its inverse applies the inverse target counit, then
`t(uH'(V.inv))`, then `t(beta_j)`. Naturality and both source and target triangles
show that these operations are inverse.
5. Define `P(zeta)` by applying `uH'` to `a`, then applying `u` to `zeta_e` and
`sigma.inv`, then composing with the inverse target unit. Put
`r = a_i ≫ Q'(theta)`. Its inverse applies the inverse target counit, then
`t(uH'(r.inv))`, then `t(delta_i)`, then `sigma_i`, then `G(theta)`.
Naturality gives `dQ(eta) ≫ r_e = a`; this and the original triangles prove that
these operations are inverse.
6. Define `gamma` by the displayed composite using `b`, `epsilon`, `sigma` and
`G(theta)`; define `k = tL(U.inv)`. Substituting the unit lift equation and using
naturality of `epsilon,sigma` gives the displayed compatibility square for `gamma`.
7. Let `M` be the original universal-counit bijection. The compatibility square and
naturality of the target unit give `P(alpha_Q' ≫ gamma) = M(B(alpha))`.
Thus `P.symm ∘ M ∘ B` is precisely the new universal-counit map, proving universality.
8. The compatibility square conjugates `gamma_(eX)` to `t(epsilon_X)` by isomorphisms.
The equivalence `t` preserves and reflects isomorphisms. The defining composite for
`gamma_Y` likewise gives invertibility exactly when `epsilon_(iY)` is invertible.
This identifies the corresponding replete classes and proves the final assertion. -/
theorem localized_universalDerivedPair_transport
    {C : Type uC} [Category.{vC} C] {C' : Type uC'} [Category.{vC'} C']
    {Lcat : Type uD} [Category.{vD} Lcat] {Lcat' : Type uD'} [Category.{vD'} Lcat']
    {H : Type uH} [Category.{vH} H] {H' : Type uH'} [Category.{vH'} H']
    (W : MorphismProperty C) (W' : MorphismProperty C')
    (Q : C ⥤ Lcat) (Q' : C' ⥤ Lcat') [Q.IsLocalization W] [Q'.IsLocalization W']
    (e : C ≌ C')
    (he : ∀ {X Y : C} (f : X ⟶ Y), W f → W' (e.functor.map f))
    (hi : ∀ {X Y : C'} (f : X ⟶ Y), W' f → W (e.inverse.map f)) :
    ∃ (D : Lcat ≌ Lcat') (a : Q ⋙ D.functor ≅ e.functor ⋙ Q')
      (b : Q' ⋙ D.inverse ≅ e.inverse ⋙ Q),
      (∀ X : C,
        D.unitIso.hom.app (Q.obj X) ≫ D.inverse.map (a.hom.app X) ≫
          b.hom.app (e.functor.obj X) = Q.map (e.unitIso.hom.app X)) ∧
      (∀ Y : C',
        D.counitIso.hom.app (Q'.obj Y) = D.functor.map (b.hom.app Y) ≫
          a.hom.app (e.inverse.obj Y) ≫ Q'.map (e.counitIso.hom.app Y)) ∧
      (∀ U : 𝟭 Lcat ⟶ D.functor ⋙ D.inverse,
        (∀ X : C, U.app (Q.obj X) ≫ D.inverse.map (a.hom.app X) ≫
          b.hom.app (e.functor.obj X) = Q.map (e.unitIso.hom.app X)) →
        U = D.unitIso.hom) ∧
      (∀ V : D.inverse ⋙ D.functor ⟶ 𝟭 Lcat',
        (∀ Y : C', V.app (Q'.obj Y) = D.functor.map (b.hom.app Y) ≫
          a.hom.app (e.inverse.obj Y) ≫ Q'.map (e.counitIso.hom.app Y)) →
        V = D.counitIso.hom) ∧
      ∀ (T : H ≌ H') (F : C ⥤ H) (G : C' ⥤ H')
        (σ : F ⋙ T.functor ≅ e.functor ⋙ G) (L : Lcat ⥤ H)
        (ε : Q ⋙ L ⟶ F), L.IsLeftDerivedFunctor ε W →
        ∃ (γ : Q' ⋙ D.inverse ⋙ L ⋙ T.functor ⟶ G)
          (k : D.functor ⋙ D.inverse ⋙ L ⋙ T.functor ≅ L ⋙ T.functor),
          (∀ Y : C', γ.app Y =
            T.functor.map (L.map (b.hom.app Y)) ≫
            T.functor.map (ε.app (e.inverse.obj Y)) ≫
            σ.hom.app (e.inverse.obj Y) ≫ G.map (e.counitIso.hom.app Y)) ∧
          (∀ Z : Lcat, k.hom.app Z =
            T.functor.map (L.map (D.unitIso.inv.app Z))) ∧
          (∀ X : C,
            (D.inverse ⋙ L ⋙ T.functor).map (a.hom.app X) ≫
              γ.app (e.functor.obj X) =
            k.hom.app (Q.obj X) ≫ T.functor.map (ε.app X) ≫ σ.hom.app X) ∧
          (D.inverse ⋙ L ⋙ T.functor).IsLeftDerivedFunctor γ W' ∧
          (∀ K : Lcat' ⥤ H',
            ∃ (B : (K ⟶ D.inverse ⋙ L ⋙ T.functor) ≃ (D.functor ⋙ K ⋙ T.inverse ⟶ L))
              (M : (D.functor ⋙ K ⋙ T.inverse ⟶ L) ≃
                (Q ⋙ D.functor ⋙ K ⋙ T.inverse ⟶ F))
              (P : (Q' ⋙ K ⟶ G) ≃ (Q ⋙ D.functor ⋙ K ⋙ T.inverse ⟶ F)),
              (∀ (α : K ⟶ D.inverse ⋙ L ⋙ T.functor) (Z : Lcat),
                (B α).app Z = T.inverse.map (α.app (D.functor.obj Z)) ≫
                  T.inverse.map (T.functor.map (L.map (D.unitIso.inv.app Z))) ≫
                  T.unitIso.inv.app (L.obj Z)) ∧
              (∀ β : D.functor ⋙ K ⋙ T.inverse ⟶ L, M β = Functor.whiskerLeft Q β ≫ ε) ∧
              (∀ (ζ : Q' ⋙ K ⟶ G) (X : C),
                (P ζ).app X = T.inverse.map (K.map (a.hom.app X)) ≫
                  T.inverse.map (ζ.app (e.functor.obj X)) ≫
                  T.inverse.map (σ.inv.app X) ≫ T.unitIso.inv.app (F.obj X)) ∧
              (∀ α : K ⟶ D.inverse ⋙ L ⋙ T.functor,
                P.symm (M (B α)) = Functor.whiskerLeft Q' α ≫ γ)) ∧
          (∀ X : C, IsIso (γ.app (e.functor.obj X)) ↔ IsIso (ε.app X)) ∧
          (∀ Y : C', IsIso (γ.app Y) ↔ IsIso (ε.app (e.inverse.obj Y))) := by
  sorry

end CategoryTheory
