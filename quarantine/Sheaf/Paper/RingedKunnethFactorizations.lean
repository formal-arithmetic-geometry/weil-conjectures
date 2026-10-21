/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedSquareTensorCompatibility
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent

/-!
# The two factorizations of the ringed-topos external product

Source: Stacks Project, Cohomology on Sites, Tags 07A7, 0B56, 0D6E;
the First identity in the blueprint unit `sk-prop-p1-adjunction-rational`
(blueprint: lem-sfb-ringed-kunneth-factorizations).

The existing ringed tensor presentations allow arbitrary models of the derived
adjunctions, identified by the unique adjunction-compatible isomorphisms. In particular
the direct-image path comparison below is conjugation, exactly as in the proof of
Stacks Tag 0D6E. No exchange or projection map is inverted.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
private theorem first_transpose
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {R : B ⥤ A} {H : B ⥤ C} {S : C ⥤ B}
    (adj : F ⊣ R) (adj' : H ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C)
    (t : T ⋙ F ⟶ (F.prod F) ⋙ U) (h : U ⋙ H ⟶ (H.prod H) ⋙ V)
    (M N : B) (Z : C) (ex : F.obj (R.obj M) ⟶ S.obj Z) :
    ((adj.comp adj').homEquiv _ _).symm
      (adj.homEquiv _ _ (t.app (R.obj M, R.obj N) ≫
          U.map (Prod.mkHom (𝟙 _) (adj.counit.app N))) ≫
        R.map (U.map (Prod.mkHom ex (𝟙 N)) ≫
          adj'.homEquiv _ _ (h.app (S.obj Z, N) ≫
            V.map (Prod.mkHom (adj'.counit.app Z) (𝟙 _))))) =
      H.map (t.app (R.obj M, R.obj N)) ≫
        h.app (F.obj (R.obj M), F.obj (R.obj N)) ≫
        V.map (Prod.mkHom (H.map ex ≫ adj'.counit.app Z)
          (H.map (adj.counit.app N))) := by
  rw [Adjunction.comp_homEquiv]
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.prod_obj]
  rw [Equiv.symm_trans_apply]
  erw [adj.homEquiv_naturality_right_symm,
    Equiv.symm_apply_apply]
  erw [adj'.homEquiv_naturality_left_symm, adj'.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply]
  simp only [Functor.map_comp, Category.assoc]
  have hn := h.naturality
    (Prod.mkHom (𝟙 (F.obj (R.obj M))) (adj.counit.app N))
  have he := h.naturality (Prod.mkHom ex (𝟙 N))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn he
  rw [reassoc_of% he, reassoc_of% hn]
  simp only [← V.map_comp]
  congr 2
  congr 1
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
private theorem second_transpose
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {R : B ⥤ A} {H : B ⥤ C} {S : C ⥤ B}
    (adj : F ⊣ R) (adj' : H ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C)
    (t : T ⋙ F ⟶ (F.prod F) ⋙ U) (h : U ⋙ H ⟶ (H.prod H) ⋙ V)
    (M N : B) (Z : C) (ex : F.obj (R.obj N) ⟶ S.obj Z) :
    ((adj.comp adj').homEquiv _ _).symm
      (adj.homEquiv _ _ (t.app (R.obj M, R.obj N) ≫
          U.map (Prod.mkHom (adj.counit.app M) (𝟙 _))) ≫
        R.map (U.map (Prod.mkHom (𝟙 M) ex) ≫
          adj'.homEquiv _ _ (h.app (M, S.obj Z) ≫
            V.map (Prod.mkHom (𝟙 _) (adj'.counit.app Z))))) =
      H.map (t.app (R.obj M, R.obj N)) ≫
        h.app (F.obj (R.obj M), F.obj (R.obj N)) ≫
        V.map (Prod.mkHom (H.map (adj.counit.app M))
          (H.map ex ≫ adj'.counit.app Z)) := by
  rw [Adjunction.comp_homEquiv]
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.prod_obj]
  rw [Equiv.symm_trans_apply]
  erw [adj.homEquiv_naturality_right_symm,
    Equiv.symm_apply_apply]
  erw [adj'.homEquiv_naturality_left_symm, adj'.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply]
  simp only [Functor.map_comp, Category.assoc]
  have hn := h.naturality
    (Prod.mkHom (adj.counit.app M) (𝟙 (F.obj (R.obj N))))
  have he := h.naturality (Prod.mkHom (𝟙 M) ex)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn he
  rw [reassoc_of% he, reassoc_of% hn]
  simp only [← V.map_comp]
  congr 2
  congr 1
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
private theorem conjugate_transpose
    {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} {R S : B ⥤ A} (adj : F ⊣ R) (adj' : G ⊣ S)
    (theta : G ≅ F) {T : A} {Z : B} (f : T ⟶ S.obj Z) :
    (adj.homEquiv _ _).symm
        (f ≫ (conjugateIsoEquiv adj adj' theta).inv.app Z) =
      theta.inv.app T ≫ (adj'.homEquiv _ _).symm f := by
  change F.map (f ≫ (conjugateEquiv adj' adj theta.inv).app Z) ≫
      adj.counit.app Z = _
  rw [Functor.map_comp, Category.assoc, conjugateEquiv_counit]
  rw [← Category.assoc, theta.inv.naturality f]
  simp only [Category.assoc, Adjunction.homEquiv_counit]

private theorem natTrans_eq_at_iso
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (a b : F ⟶ G) {X Y : A} (i : X ≅ Y) (h : a.app X = b.app X) :
    a.app Y = b.app Y := by
  rw [← cancel_epi (F.map i.hom), a.naturality, b.naturality, h]

namespace SheafOfModules

private abbrev CornerModules (A : RingedTensorCorner.{u, w}) :=
  SheafOfModules.{u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem square_tensor
    {Y X Y' X' : RingedTensorCorner.{u, w}}
    {f : RingedTensorEdge Y X} {g : RingedTensorEdge Y Y'}
    {h : RingedTensorEdge X X'} {k : RingedTensorEdge Y' X'}
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (aY : RingedTensorModel Y) (aX : RingedTensorModel X)
    (aY' : RingedTensorModel Y') (aX' : RingedTensorModel X')
    (V W : DerivedCategory (CornerModules Y)) :
    s.derivedComparison.hom.app (Y.tensor.obj (V, W)) ≫
        h.left.map ((f.tensorComparison aY aX).hom.app (V, W)) ≫
        (h.tensorComparison aX aX').hom.app (f.left.obj V, f.left.obj W) =
      k.left.map ((g.tensorComparison aY aY').hom.app (V, W)) ≫
        (k.tensorComparison aY' aX').hom.app (g.left.obj V, g.left.obj W) ≫
        X'.tensor.map (Prod.mkHom (s.derivedComparison.hom.app V)
          (s.derivedComparison.hom.app W)) := by
  let l : Y.tensor ⋙ g.left ⋙ k.left ⟶
      ((f.left ⋙ h.left).prod (f.left ⋙ h.left)) ⋙ X'.tensor :=
    Functor.whiskerLeft Y.tensor s.derivedComparison.hom ≫
      Functor.whiskerRight (f.tensorComparison aY aX).hom h.left ≫
        Functor.whiskerLeft (f.left.prod f.left) (h.tensorComparison aX aX').hom
  let r : Y.tensor ⋙ g.left ⋙ k.left ⟶
      ((f.left ⋙ h.left).prod (f.left ⋙ h.left)) ⋙ X'.tensor :=
    Functor.whiskerRight (g.tensorComparison aY aY').hom k.left ≫
      Functor.whiskerLeft (g.left.prod g.left) (k.tensorComparison aY' aX').hom ≫
        Functor.whiskerRight
          (NatTrans.prod s.derivedComparison.hom s.derivedComparison.hom) X'.tensor
  have hlr : l = r := by
    obtain ⟨P, hP, _, _, hd⟩ := site_derived_tensor_descent.{u, w, u + 1, w} Y.topology Y.ring
    apply (hd _ inferInstance _ _).injective
    ext Z
    obtain ⟨hp, hpf⟩ := (hP Z.1.obj).1 Z.1.property
    obtain ⟨hq, hqf⟩ := (hP Z.2.obj).1 Z.2.property
    have he : l.app (DerivedCategory.Q.obj Z.1.obj.as,
        DerivedCategory.Q.obj Z.2.obj.as) = r.app
        (DerivedCategory.Q.obj Z.1.obj.as, DerivedCategory.Q.obj Z.2.obj.as) :=
      ringedSquareTensorCompatibility s aY aX aY' aX' s.derivedComparison
        (Classical.choose_spec s.derivedComparison_existsUnique.exists)
        Z.1.obj.as Z.2.obj.as hp hpf hq hqf
    exact natTrans_eq_at_iso l r
      (((DerivedCategory.quotientCompQhIso (CornerModules Y)).app Z.1.obj.as).symm.prod
        ((DerivedCategory.quotientCompQhIso (CornerModules Y)).app Z.2.obj.as).symm) he
  exact congr_app hlr (V, W)

/-- Projection with the fixed factor first: the adjunct of identity tensor counit.
This is the usual projection map with tensor symmetry putting its factors in this order.
Source: Stacks Tag 0B56, equation-projection-formula-map
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def RingedTensorEdge.projectionFixedFirst
    {Y X : RingedTensorCorner.{u, w}} (f : RingedTensorEdge Y X)
    (aY : RingedTensorModel Y) (aX : RingedTensorModel X)
    (Q : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)))
    (E : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose X.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X.ring))) :
    Y.tensor.obj (Q, f.right.obj E) ⟶ f.right.obj (X.tensor.obj (f.left.obj Q, E)) :=
  f.derivedAdjunction.homEquiv _ _
    ((f.tensorComparison aY aX).hom.app (Q, f.right.obj E) ≫
      X.tensor.map (CategoryTheory.Prod.mkHom (𝟙 (f.left.obj Q))
        (f.derivedAdjunction.counit.app E)))

namespace RingedKunneth

variable {Y X W : RingedTensorCorner.{u, w}}
  {q : RingedTensorEdge Y X} {a b : RingedTensorEdge X W}

/-- The opposite exchange map bar-beta: LR → SB, using the inverse comparison.
Source: Stacks Tag 07A7, remark-base-change
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def betaBar (s : RingedTensorSquare Y X X W q q a b) :
    q.right ⋙ q.left ⟶ b.left ⋙ a.right :=
  (mateEquiv q.derivedAdjunction a.derivedAdjunction
    (TwoSquare.mk q.left q.left a.left b.left s.derivedComparison.inv)).natTrans

/-- The canonical path comparison RS ≅ RU, obtained by uniqueness of right adjoints
from BL ≅ AL. This is the composition comparison of Stacks Tag 0D6E, whose proof
constructs it by precisely this conjugation of pullback composition comparisons.
Source: Stacks Tag 0D6E, lemma-derived-pushforward-composition
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def directComparison (s : RingedTensorSquare Y X X W q q a b) :
    a.right ⋙ q.right ≅ b.right ⋙ q.right :=
  conjugateIsoEquiv (q.derivedAdjunction.comp a.derivedAdjunction)
    (q.derivedAdjunction.comp b.derivedAdjunction) s.derivedComparison

variable (s : RingedTensorSquare Y X X W q q a b)
  (aY : RingedTensorModel Y) (aX : RingedTensorModel X) (aW : RingedTensorModel W)
  (M N : DerivedCategory (SheafOfModules.{u}
    ((sheafCompose X.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X.ring)))

/-- First route: projection for q, beta tensor identity, then projection for b.
Its target is RU(AM tensor BN), before the canonical comparison with RS.
Source: Stacks Tags 07A7, 0B56; blueprint First identity
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def first :
    Y.tensor.obj (q.right.obj M, q.right.obj N) ⟶
      q.right.obj (b.right.obj (W.tensor.obj (a.left.obj M, b.left.obj N))) :=
  q.projectionFixedFirst aY aX (q.right.obj M) N ≫
    q.right.map (X.tensor.map (CategoryTheory.Prod.mkHom (s.exchange.app M) (𝟙 N)) ≫
      b.projection aX aW (a.left.obj M) N)

/-- Second route: projection for q, identity tensor bar-beta, then projection for a
with the fixed factor first. Its target is RS(AM tensor BN).
Source: Stacks Tags 07A7, 0B56; blueprint First identity
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def second :
    Y.tensor.obj (q.right.obj M, q.right.obj N) ⟶
      q.right.obj (a.right.obj (W.tensor.obj (a.left.obj M, b.left.obj N))) :=
  q.projection aY aX M (q.right.obj N) ≫
    q.right.map (X.tensor.map (CategoryTheory.Prod.mkHom (𝟙 M) ((betaBar s).app N)) ≫
      a.projectionFixedFirst aX aW M (b.left.obj N))

/-- The mixed tensor of the two original counits. The first two arrows are the tensor
comparison for AL; theta inverse changes the second factor from ALRN to BLRN.
Thus the source is (qa)* applied to RM tensor RN, in its composite pullback model.
Source: Stacks Tags 07A7, 0B56; the two-counit expansion of the blueprint First identity
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def commonTranspose :
    a.left.obj (q.left.obj (Y.tensor.obj (q.right.obj M, q.right.obj N))) ⟶
      W.tensor.obj (a.left.obj M, b.left.obj N) :=
  a.left.map ((q.tensorComparison aY aX).hom.app (q.right.obj M, q.right.obj N)) ≫
    (a.tensorComparison aX aW).hom.app
      (q.left.obj (q.right.obj M), q.left.obj (q.right.obj N)) ≫
    W.tensor.map (CategoryTheory.Prod.mkHom
      (a.left.map (q.derivedAdjunction.counit.app M))
      (s.derivedComparison.inv.app (q.right.obj N) ≫
        b.left.map (q.derivedAdjunction.counit.app N)))

end RingedKunneth

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- The composite functor and adjunction transports need additional elaboration steps.
/-- The two projection/exchange factorizations agree, and their common transpose is
the displayed mixed tensor of the original q-counits.

Source: Stacks Tags 07A7, 0B56, 0D6E; blueprint First identity
(blueprint: lem-sfb-ringed-kunneth-factorizations).

Proof plan, following the node's six steps:
1. Apply lem-sfb-ringed-comparison-tensor-adjunction to the two paths (a,q), (b,q).
   Its tensor identity says theta intertwines the composite tensor comparisons d_B,d_A.
   Its adjunction compatibility identifies the canonical direct-image comparison with
   the conjugate used by directComparison (Stacks 0D6E).
2. The mate equations from def-weil-pbc-adjunction-mate give
   w_AM B(beta_M) = A(v_M) theta_RM and
   s_BN A(bar-beta_N) = B(v_N) theta_RN inverse.
3. Transpose first successively under q and b, using
   def-weil-pbc-composite-adjunction. The definition of projection from
   lem-weil-pbc-ringed-exchange-tensor-coherence, counit naturality, and naturality of
   the canonical tensor comparisons rewrite its transpose as
   (A(v_M) theta_RM tensor B(v_N)) d_B.
4. Transpose second under q and a. The same identities give
   (A(v_M) tensor B(v_N) theta_RN inverse) d_A.
5. Apply the tensor identity from step 1 and cancel theta on the first factor.
   The first transpose precomposed with theta inverse becomes the second transpose,
   precisely commonTranspose. This proves the second conjunct.
6. The conjugate comparison satisfies the composite-counit equation. Thus transporting
   first by directComparison inverse corresponds to precomposing its transpose with
   theta inverse. Injectivity of the composite hom-equivalence now proves the first
   conjunct. No beta, bar-beta or projection map is inverted, and neither a relation
   between M and N nor cartesianness, properness or boundedness is used. -/
theorem ringedKunnethFactorizations
    {Y X W : RingedTensorCorner.{u, w}}
    {q : RingedTensorEdge Y X} {a b : RingedTensorEdge X W}
    (s : RingedTensorSquare Y X X W q q a b)
    (aY : RingedTensorModel Y) (aX : RingedTensorModel X) (aW : RingedTensorModel W)
    (M N : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose X.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X.ring))) :
    (RingedKunneth.first s aY aX aW M N ≫
        (RingedKunneth.directComparison s).inv.app
          (W.tensor.obj (a.left.obj M, b.left.obj N)) =
      RingedKunneth.second s aY aX aW M N) ∧
    ((q.derivedAdjunction.comp a.derivedAdjunction).homEquiv _ _).symm
        (RingedKunneth.second s aY aX aW M N) =
      RingedKunneth.commonTranspose s aY aX aW M N := by
  have hex := mateEquiv_counit q.derivedAdjunction b.derivedAdjunction
    (TwoSquare.mk q.left q.left b.left a.left s.derivedComparison.hom) M
  have hbar := mateEquiv_counit q.derivedAdjunction a.derivedAdjunction
    (TwoSquare.mk q.left q.left a.left b.left s.derivedComparison.inv) N
  change b.left.map (s.exchange.app M) ≫ b.derivedAdjunction.counit.app (a.left.obj M) =
    s.derivedComparison.hom.app (q.right.obj M) ≫
      a.left.map (q.derivedAdjunction.counit.app M) at hex
  change a.left.map ((RingedKunneth.betaBar s).app N) ≫
      a.derivedAdjunction.counit.app (b.left.obj N) =
    s.derivedComparison.inv.app (q.right.obj N) ≫
      b.left.map (q.derivedAdjunction.counit.app N) at hbar
  have hF := first_transpose q.derivedAdjunction b.derivedAdjunction
    Y.tensor X.tensor W.tensor (q.tensorComparison aY aX).hom
    (b.tensorComparison aX aW).hom M N (a.left.obj M) (s.exchange.app M)
  change ((q.derivedAdjunction.comp b.derivedAdjunction).homEquiv _ _).symm
      (RingedKunneth.first s aY aX aW M N) = _ at hF
  rw [hex] at hF
  have hG := second_transpose q.derivedAdjunction a.derivedAdjunction
    Y.tensor X.tensor W.tensor (q.tensorComparison aY aX).hom
    (a.tensorComparison aX aW).hom M N (b.left.obj N)
    ((RingedKunneth.betaBar s).app N)
  change ((q.derivedAdjunction.comp a.derivedAdjunction).homEquiv _ _).symm
      (RingedKunneth.second s aY aX aW M N) = _ at hG
  rw [hbar] at hG
  have hG' : ((q.derivedAdjunction.comp a.derivedAdjunction).homEquiv _ _).symm
      (RingedKunneth.second s aY aX aW M N) =
      RingedKunneth.commonTranspose s aY aX aW M N := hG
  refine ⟨?_, hG'⟩
  apply ((q.derivedAdjunction.comp a.derivedAdjunction).homEquiv _ _).symm.injective
  rw [hG']
  change ((q.derivedAdjunction.comp a.derivedAdjunction).homEquiv _ _).symm
      (RingedKunneth.first s aY aX aW M N ≫
        (conjugateIsoEquiv (q.derivedAdjunction.comp a.derivedAdjunction)
          (q.derivedAdjunction.comp b.derivedAdjunction) s.derivedComparison).inv.app _) = _
  rw [conjugate_transpose (q.derivedAdjunction.comp a.derivedAdjunction)
    (q.derivedAdjunction.comp b.derivedAdjunction) s.derivedComparison, hF]
  have hc := square_tensor s aY aX aX aW (q.right.obj M) (q.right.obj N)
  apply (cancel_epi (s.derivedComparison.hom.app
    (Y.tensor.obj (q.right.obj M, q.right.obj N)))).1
  simp only [RingedKunneth.commonTranspose, ← Category.assoc]
  rw [Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  simp only [← W.tensor.map_comp]
  congr 2
  congr 1
  ext <;> simp


end SheafOfModules
