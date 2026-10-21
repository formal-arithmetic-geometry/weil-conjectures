/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transport of ordinary horizontal pasting

Source: Stacks Project, Tag 0F7D (lemma-shriek-proper-and-open-compose-horizontal),
and the categorical comparison calculation extracted from the local-pairs construction
(blueprint: lem-sp-ordinary-horizontal-pasting-transport).

The respected-cell and compositor equations are expanded componentwise. This avoids
choices of parenthesization: canonical functor associators have identity components.
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uC uD uE uF uA' uB' uC' uD' uE' uF'
universe vA vB vC vD vE vF vA' vB' vC' vD' vE' vF'

namespace CategoryTheory

/-- Coherent invertible comparisons transport a primed horizontal-pasting equation to
an equality after realization, without any faithfulness hypothesis.
Source: Stacks Project, Tag 0F7D (lemma-shriek-proper-and-open-compose-horizontal),
agent categorical transport calculation
(blueprint: lem-sp-ordinary-horizontal-pasting-transport).

Proof:
1. Fix `N` and expand the composite comparisons `s = e_QJI`, `u = e_QI₁₂`,
   `v = e_LKR`, `w = e_LPI`, and `t = e_K₁₂R` using the stated composite convention.
   Functoriality and associativity identify the two triple parenthesizations.
2. Naturality of `eQ` at `ci.hom.app N`, followed by `hi N`, transports the lower
   compositor. Combine this with `hc N` to identify the outer path, postcomposed
   with `t`, as `s` followed by the primed lower compositor and `c'`.
3. Apply `hk` at `R.obj N` and naturality of `ck'` at `eR.hom.app N` to transport
   the upper compositor: its realized component followed by `t` equals `v`
   followed by the corresponding primed compositor.
4. Naturality of `eL` at `a.app N`, followed by `L'` applied to `ha N`, transports
   left whiskering of `a`, identifying its realized component followed by `v`
   with `w` followed by `L'.map (a'.app (EC.obj N))`.
5. Apply `hb` at `I.obj N` and naturality of `b'` at `eI.hom.app N` to transport
   right whiskering of `b`: its realized component followed by `w` equals `s`
   followed by `b'.app (I'.obj (EC.obj N))`.
6. Combine steps 3--5 and use `hstrict (EC.obj N)` to identify this path with
   step 2. Cancel the invertible `t`, whose inverse is the composite of
   `K₁₂'.map (eR.inv.app N)` with `eK₁₂.inv.app (R.obj N)`. No equality is
   reflected through `EE`.
-/
theorem ordinaryHorizontalPastingTransport
    {A : Type uA} {B : Type uB} {C : Type uC}
    {D : Type uD} {E : Type uE} {F : Type uF}
    {A' : Type uA'} {B' : Type uB'} {C' : Type uC'}
    {D' : Type uD'} {E' : Type uE'} {F' : Type uF'}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    [Category.{vD} D] [Category.{vE} E] [Category.{vF} F]
    [Category.{vA'} A'] [Category.{vB'} B'] [Category.{vC'} C']
    [Category.{vD'} D'] [Category.{vE'} E'] [Category.{vF'} F']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'}
    {ED : D ⥤ D'} {EE : E ⥤ E'} {EF : F ⥤ F'}
    {K : A ⥤ B} {L : B ⥤ E} {I : C ⥤ D} {J : D ⥤ F}
    {R : C ⥤ A} {P : D ⥤ B} {Q : F ⥤ E}
    {K₁₂ : A ⥤ E} {I₁₂ : C ⥤ F}
    {K' : A' ⥤ B'} {L' : B' ⥤ E'} {I' : C' ⥤ D'} {J' : D' ⥤ F'}
    {R' : C' ⥤ A'} {P' : D' ⥤ B'} {Q' : F' ⥤ E'}
    {K₁₂' : A' ⥤ E'} {I₁₂' : C' ⥤ F'}
    (eR : R ⋙ EA ≅ EC ⋙ R') (eP : P ⋙ EB ≅ ED ⋙ P')
    (eQ : Q ⋙ EE ≅ EF ⋙ Q')
    (eK : K ⋙ EB ≅ EA ⋙ K') (eL : L ⋙ EE ≅ EB ⋙ L')
    (eI : I ⋙ ED ≅ EC ⋙ I') (eJ : J ⋙ EF ≅ ED ⋙ J')
    (eK₁₂ : K₁₂ ⋙ EE ≅ EA ⋙ K₁₂') (eI₁₂ : I₁₂ ⋙ EF ≅ EC ⋙ I₁₂')
    (ck : K ⋙ L ≅ K₁₂) (ci : I ⋙ J ≅ I₁₂)
    (ck' : K' ⋙ L' ≅ K₁₂') (ci' : I' ⋙ J' ≅ I₁₂')
    (a : TwoSquare I R P K) (b : TwoSquare J P Q L)
    (c : TwoSquare I₁₂ R Q K₁₂)
    (a' : TwoSquare I' R' P' K') (b' : TwoSquare J' P' Q' L')
    (c' : TwoSquare I₁₂' R' Q' K₁₂')
    (hk : ∀ M : A, EE.map (ck.hom.app M) ≫ eK₁₂.hom.app M =
      eL.hom.app (K.obj M) ≫ L'.map (eK.hom.app M) ≫ ck'.hom.app (EA.obj M))
    (hi : ∀ N : C, EF.map (ci.hom.app N) ≫ eI₁₂.hom.app N =
      eJ.hom.app (I.obj N) ≫ J'.map (eI.hom.app N) ≫ ci'.hom.app (EC.obj N))
    (ha : ∀ N : C, EB.map (a.app N) ≫ eK.hom.app (R.obj N) ≫
        K'.map (eR.hom.app N) =
      eP.hom.app (I.obj N) ≫ P'.map (eI.hom.app N) ≫ a'.app (EC.obj N))
    (hb : ∀ M : D, EE.map (b.app M) ≫ eL.hom.app (P.obj M) ≫
        L'.map (eP.hom.app M) =
      eQ.hom.app (J.obj M) ≫ Q'.map (eJ.hom.app M) ≫ b'.app (ED.obj M))
    (hc : ∀ N : C, EE.map (c.app N) ≫ eK₁₂.hom.app (R.obj N) ≫
        K₁₂'.map (eR.hom.app N) =
      eQ.hom.app (I₁₂.obj N) ≫ Q'.map (eI₁₂.hom.app N) ≫ c'.app (EC.obj N))
    (hstrict : ∀ N' : C', Q'.map (ci'.hom.app N') ≫ c'.app N' =
      b'.app (I'.obj N') ≫ L'.map (a'.app N') ≫ ck'.hom.app (R'.obj N'))
    (N : C) :
    EE.map (Q.map (ci.hom.app N) ≫ c.app N) =
      EE.map (b.app (I.obj N) ≫ L.map (a.app N) ≫ ck.hom.app (R.obj N)) := by
  sorry

end CategoryTheory
