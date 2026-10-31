/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactFiberStalkBaseChangeData
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement

/-!
# Coherence obligation for compact-support stalk base change
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

-- The public normalization theorem has extra geometric hypotheses; its formal proof does not.
private theorem exchange_normalization_noqc
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    (sq : IsPullback v' f' f v) (c : Compactification f) :
    unboundedEtaleCompactSupportExchange A sq c =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g v).toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A)
          (c.isPullback_i_ofIsPullback sq)).inv
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) (c.ofIsPullback sq).g) ≫
      (Functor.associator _ _ _).hom := by
  ext K
  have h := congrArg (fun η ↦ η.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K))
    (exact_exchange_transport A (IsPullback.of_hasPullback c.g v).toCommSq)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simp only [unboundedEtaleCompactSupportExchange,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap,
    derivedOpenImmersionLowerShriekBaseChangeIso, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
    Functor.comp_obj, Functor.comp_map] at h ⊢
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.map_comp]
  rw [← h]
  simp only [Category.assoc]
  rw [((openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (c.ofIsPullback sq).i).mapDerivedCategory).map_id]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id]
  rfl

private lemma shriek_base_change_general_noqc
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [(unboundedFormalism A).HasProperExchange]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    (sq : IsPullback v' f' f v)
    (c : Compactification f) :
    ((unboundedFormalism A).shriekBaseChangeOfIsPullback sq c).natTrans =
      unboundedEtaleCompactSupportExchange A sq c := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := unboundedFormalism A) (c.isPullback_i_ofIsPullback sq)
  have hh : inv ((unboundedFormalism A).baseChange v' (c.ofIsPullback sq).i c.i
      (pullback.fst c.g v) (c.isPullback_i_ofIsPullback sq).w).natTrans =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [unbounded_open_base_change]
    exact Iso.hom_inv_id _
  rw [exchange_normalization_noqc]
  dsimp only [CompactSupportFormalism.shriekBaseChangeOfIsPullback,
    CompactSupportFormalism.shriekBaseChange, ExchangeFormalism.shriekBaseChange,
    TwoSquare.hComp, TwoSquare.natTrans, TwoSquare.mk]
  rw [unbounded_pf_base_change, hh]
  rfl

/-- Horizontal pasting for compactification base-change maps at a fixed object, without
geometric finiteness hypotheses. This is the underlying morphism calculation used by the
compact-fibre stalk square. -/
private theorem compactification_paste
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' T : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ T}
    {g : Y' ⟶ Y} {gE : X' ⟶ X} {b' : T ⟶ Y'} {bE : X'' ⟶ X'}
    [QuasiCompact f'']
    (sq : IsPullback gE f' f g) (sq' : IsPullback bE f'' f' b')
    (sqd : IsPullback (bE ≫ gE) f'' f (b' ≫ g))
    (c : Compactification f)
    (K : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b' g (b' ≫ g)).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.obj
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K)) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) b').leftDerivedFunctor.map
        ((Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app K) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq' (c.ofIsPullback sq)).app
        ((Etale.upperStar (ModuleCat.{u + 1} A) gE).leftDerivedFunctor.obj K) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} A)
          ((c.ofIsPullback sq).ofIsPullback sq').g).rightDerivedFunctor.map
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
            ((c.ofIsPullback sq).ofIsPullback sq').i).mapDerivedCategory.map
          ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) bE gE (bE ≫ gE)).inv.app K)) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationIso A
          ((c.ofIsPullback sq).ofIsPullback sq') (c.ofIsPullback sqd)).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) (bE ≫ gE)).leftDerivedFunctor.obj K) =
    (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sqd c).app K := by
  let := unbounded_has_proper_exchange A
  have hsqd : sqd = sq'.paste_horiz sq := Subsingleton.elim _ _
  cases hsqd
  let F := unboundedFormalism A
  let cp := c.ofIsPullback sq
  let cpp := cp.ofIsPullback sq'
  let h₁ : cpp.Z ⟶ cp.Z := pullback.fst cp.g b'
  let h₂ : cp.Z ⟶ c.Z := pullback.fst c.g g
  have hi₁ := cp.isPullback_i_ofIsPullback sq'
  have hp₁ := (cp.isPullback_g_ofIsPullback sq').flip
  have hi₂ := c.isPullback_i_ofIsPullback sq
  have hp₂ := (c.isPullback_g_ofIsPullback sq).flip
  have hi := hi₁.paste_horiz hi₂
  have hp := hp₁.paste_horiz hp₂
  have h := congrArg TwoSquare.natTrans
    (F.shriekBaseChange_paste_horiz c cp cpp h₁ h₂ hi₁ hp₁ hi₂ hp₂ hi hp)
  rw [shriekBaseChange_arbitrary F (sq'.paste_horiz sq) c cpp (h₁ ≫ h₂) hi hp] at h
  change (_ ≫ _) =
    ((((F.shriekBaseChangeOfIsPullback sq c).vComp
      (F.shriekBaseChangeOfIsPullback sq' cp)).whiskerLeft
        (F.pbComp' bE gE (bE ≫ gE) rfl).inv).whiskerRight
          (F.pbComp' b' g (b' ≫ g) rfl).hom).natTrans at h
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp] at h
  rw [shriek_base_change_general_noqc A (sq'.paste_horiz sq) c,
    shriek_base_change_general_noqc A sq c,
    shriek_base_change_general_noqc A sq' cp] at h
  rw [unbounded_pb_comp', unbounded_pb_comp', unbounded_shriek_iso] at h
  have hh := congr_app h K
  simp only [TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc] at hh
  let cd := c.ofIsPullback (sq'.paste_horiz sq)
  let e := rightDerivedLowerShriekOfCompactificationIso A cd cpp
  change (unboundedEtaleCompactSupportExchange A (sq'.paste_horiz sq) c).app K ≫
      e.hom.app ((upperStar (ModuleCat.{u + 1} A) (bE ≫ gE)).mapDerivedCategory.obj K) =
    (exact_pb_comp A b' g).hom.app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) b').mapDerivedCategory.map
        ((unboundedEtaleCompactSupportExchange A sq c).app K) ≫
      (unboundedEtaleCompactSupportExchange A sq' cp).app
        ((upperStar (ModuleCat.{u + 1} A) gE).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cpp).map
        ((exact_pb_comp A bE gE).inv.app K) at hh
  have he : rightDerivedLowerShriekOfCompactificationIso A cpp cd = e.symm := by
    dsimp only [e]
    rw [← unbounded_shriek_iso, ← unbounded_shriek_iso]
    exact (F.shriekIso_symm cd cpp).symm
  change _ ≫ _ ≫ _ ≫ (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) cpp).map _ ≫
      (rightDerivedLowerShriekOfCompactificationIso A cpp cd).hom.app _ = _
  rw [he]
  apply (cancel_mono (e.hom.app
    ((upperStar (ModuleCat.{u + 1} A) (bE ≫ gE)).leftDerivedFunctor.obj K))).mp
  simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id_app, Category.comp_id]
  apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) (b' ≫ g)).inv.app _)).mp
  apply (cancel_mono ((rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} A) cpp).map
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) (bE ≫ gE)).hom.app K))).mp
  simp only [Category.assoc]
  rw [← e.hom.naturality]
  simp only [unboundedEtaleCompactSupportExchange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] at hh
  erw [hh]
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.map_comp]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Category.comp_id]
  simp only [exact_pb_comp, Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    Iso.trans_inv, NatTrans.comp_app]
  simp only [Functor.map_comp, Category.assoc]
  have hn :=
    (upperStar (ModuleCat.{u + 1} A) b').leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cp).map
      ((upperStar (ModuleCat.{u + 1} A) gE).leftDerivedFunctorIsoMapDerivedCategory.hom.app K))
  erw [reassoc_of% hn]
  have hn₂ := (rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} A) sq' cp).naturality
      ((upperStar (ModuleCat.{u + 1} A) gE).leftDerivedFunctorIsoMapDerivedCategory.hom.app K)
  simp only [Functor.comp_map] at hn₂
  erw [reassoc_of% hn₂]
  rw [← Functor.map_comp_assoc]
  erw [←
    (upperStar (ModuleCat.{u + 1} A) bE).leftDerivedFunctorIsoMapDerivedCategory.hom.naturality]
  simp only [Functor.map_comp, Category.assoc]
  have hlast :=
    (upperStar (ModuleCat.{u + 1} A) b').leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
      ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq c).app K)
  simp only [Functor.comp_obj] at hlast
  erw [← reassoc_of% hlast]
  rfl

end AlgebraicGeometry.Etale

namespace WeilConjectures

/-- The unbounded compactification exchange square, evaluated by derived sections
on `T`. Source: latest blueprint, thm-pur-rank-one-thom.proof.md, Step 3
(parent: lem-pur-cfiber-stalk-base-change). For `T = Spec Ω` these are the
stalk and compact-fibre comparisons of lem-pur-cfiber-stalk. The outer square
uses the iterated fibre as its pullback object; its `isoPullback` is precisely
`compactFiberStalkFibreIso`. The final comparison transports the iterated
compactification to the compactification of that outer square.
(blueprint: lem-pur-cfiber-stalk-base-change-square-coherence)

Proof. Expand each exchange map `Ex_!(sq, c)` as the proper base-change mate
`Ex_*` for `c.g`, whiskered by `Di_!`, followed by the inverse of the
open-extension base-change isomorphism. Horizontal pasting of the derived proper
base-change mates (thm-cbc-finite-torsion, pasting clause) identifies the composite
of the mates for `sq` and `sq'`, joined by the inverse-image compositor
`leftDerivedUpperStarComp`, with the mate for the pasted square. The
open-extension isomorphisms paste in the same way, because base change of an open
immersion along a composite is the composite of the base changes. The iterated
base-changed compactification `(c ×_Y Y') ×_{Y'} T` and the direct one `c ×_Y T`
of `sqd` are compactifications of the same `f''`; the comparison
`rightDerivedLowerShriekOfCompactificationIso` through their common refinement is
compatible with the two exchange maps, since both factor through the canonical
isomorphism of the iterated and direct fibre products of `c.Z`. Applying
`RΓ(T, -)` gives the equation. -/
theorem compactFiberStalkBaseChangeSquare_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' T : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ T}
    {g : Y' ⟶ Y} {gE : X' ⟶ X} {b' : T ⟶ Y'} {bE : X'' ⟶ X'}
    [QuasiCompact f'']
    (sq : IsPullback gE f' f g) (sq' : IsPullback bE f'' f' b')
    (sqd : IsPullback (bE ≫ gE) f'' f (b' ≫ g))
    (c : Compactification f)
    (K : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    compactFiberStalkBaseChangeSquare A sq sq' sqd c K := by
  unfold compactFiberStalkBaseChangeSquare
  exact congrArg (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} A) T).map
    (Etale.compactification_paste A sq sq' sqd c K)

end WeilConjectures
