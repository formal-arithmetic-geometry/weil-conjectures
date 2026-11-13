/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # The canonical section comparison and the étale unit

## References

* [Stacks, Tag 09ZF], [Stacks, Tags 03CB, 03CC]
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem isoTrans_apply {A B C : Type (u + 1)} (e : A ≅ B) (f : B ≅ C)
    (x : A) : (e ≪≫ f).hom x = f.hom (e.hom x) := rfl

private theorem sheafIso_apply {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {F G : Sheaf J (Type (u + 1))} (e : F ≅ G)
    (U : Cᵒᵖ) (s : F.obj.obj U) :
    (((sheafToPresheaf J (Type (u + 1))).mapIso e).app U).hom s =
      e.hom.hom.app U s := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Core section-isomorphism/unit identity used by the top-open comparison. -/
theorem gabber_h0_zariski_section_unit_equation
    {X Z X' : Scheme.{u}} (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    gabberZariskiCompare i h F ∘
      (((Scheme.etaleSetPullback (pullback.snd i h)).obj
        ((Scheme.etaleSetPullback h).obj F)).obj.map
          (gabberPreimageEtaleIso (pullback.snd i h) ⊤).hom.op) ∘
      (etaleSetDescentUnit (pullback.snd i h)
        ((Scheme.etaleSetPullback h).obj F) (Scheme.Etale.mk (⊤ : X'.Opens).ι)) =
      fun s : (gabberZariskiG h F).obj.obj (op (⊤ : X'.Opens)) ↦
        eqToHom (congrArg
          (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
              (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)
          (etaleSetDescentComparison h (pullback.snd i h) F
            (Scheme.Etale.mk (𝟙 X)) (gabberZariskiLift h F s)) := by
  let j := pullback.snd i h
  let B := MorphismProperty.Over.pullback @Etale ⊤ j
  let H := (Scheme.etaleSetPullback h).obj F
  let K := (Scheme.etaleSetPullback j).obj H
  let a := gabberTopEtaleIso (pullback i h) ≪≫ gabberIdentityEtaleIso j ≪≫
    B.mapIso (gabberIdentityEtaleIso h)
  -- The second projection is an isomorphism because the top-open inclusion is.
  have he : a.inv ≫ (gabberPreimageEtaleIso j ⊤).hom =
      B.map (gabberTopPullbackIso h).inv := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (pullback.snd (⊤ : X'.Opens).ι j)).1
    exact (MorphismProperty.Over.w
      (a.inv ≫ (gabberPreimageEtaleIso j ⊤).hom)).trans
        (MorphismProperty.Over.w (B.map (gabberTopPullbackIso h).inv)).symm
  funext s
  -- Naturality of the unit moves the top-open lift through inverse image.
  have hn := etaleSetInverseImageCompositionUnits.1 X' (pullback i h) j H
    (Scheme.Etale.mk (⊤ : X'.Opens).ι)
    ((MorphismProperty.Over.pullback @Etale ⊤ h).obj (Scheme.Etale.mk (𝟙 X)))
    (gabberTopPullbackIso h).inv s
  change etaleSetDescentUnit j H _ (H.obj.map (gabberTopPullbackIso h).inv.op s) =
    K.obj.map (B.map (gabberTopPullbackIso h).inv).op
      (etaleSetDescentUnit j H _ s) at hn
  have hk : K.obj.map a.inv.op
      (K.obj.map (gabberPreimageEtaleIso j ⊤).hom.op
        (etaleSetDescentUnit j H _ s)) =
      etaleSetDescentUnit j H _ (H.obj.map (gabberTopPullbackIso h).inv.op s) := by
    have hm := congrArg (fun m ↦ K.obj.map m.op (etaleSetDescentUnit j H _ s)) he
    simp only [op_comp, Functor.map_comp, comp_apply] at hm
    exact hm.trans hn.symm
  -- Keep the three outer factors together while transporting the inner equality.
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2
  let P := (Scheme.etaleSetPullback (j ≫ h)).obj F
  let d := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) j h
  let A := B.obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
    (Scheme.Etale.mk (𝟙 X)))
  let e := (((sheafToPresheaf _ _).mapIso
      ((c X X' (pullback i h) h j).app F)).app (op A)) ≪≫
    P.obj.mapIso ((d.app (Scheme.Etale.mk (𝟙 X))).op) ≪≫
    eqToIso (congrArg
      (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
          (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)
  -- Focused rewrites avoid unfolding the transport on the other side.
  conv_lhs =>
    rw [Function.comp_apply, Function.comp_apply]
  conv_lhs =>
    unfold gabberZariskiCompare gabberZariskiSectionIso
    rw [isoTrans_apply]
  conv_lhs =>
    change e.hom (K.obj.map a.inv.op
      (K.obj.map (gabberPreimageEtaleIso j ⊤).hom.op (etaleSetDescentUnit j H _ s)))
    rw [hk]
  conv_lhs =>
    dsimp only [e, P, d, A, B, c, H, j]
    rw [isoTrans_apply, isoTrans_apply]
  conv_rhs =>
    arg 2
    unfold etaleSetDescentComparison
    arg 2
    arg 2
    arg 2
    unfold gabberZariskiLift
  conv_lhs =>
    arg 1
    rw [eqToIso.hom]
  conv_lhs =>
    arg 2
    arg 1
    rw [Functor.mapIso_hom, Iso.op_hom, Iso.app_hom]
  conv_lhs =>
    arg 2
    arg 2
    rw [sheafIso_apply, Iso.app_hom]
  with_reducible congr 3
  all_goals simp only [sheafToPresheaf, ObjectProperty.ι_obj, Functor.comp_obj]

end AlgebraicGeometry
