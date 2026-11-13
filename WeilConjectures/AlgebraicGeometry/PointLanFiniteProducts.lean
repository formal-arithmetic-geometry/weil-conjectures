/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor

import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps

/-! # Finite coproducts for the point Kan presheaf

## References

* Bhatt–Scholze, Lemma 4.2.13(1).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
/-- Finite affine coproducts induce product cones for point Kan extensions. -/
theorem point_lan_finite_products (X : Scheme.{u}) (C : Type w) [Category.{v} C]
    (F : Sheaf (coherentTopology Profinite.{u}) C) (P : X.ProEtᵒᵖ ⥤ C)
    (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P)
    (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
    (I : Type u) [Finite I] (U : I → X.ProEt)
    (ha : ∀ i, IsAffine (U i).left)
    (hw : ∀ i,
      ∀ (A B : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : A ⟶ B),
        Epi f → Function.Surjective (f.hom.app (op (U i)))) :
    ∃ c : Cofan U, Nonempty (IsColimit c) ∧
      Nonempty (IsLimit (Fan.mk (P.obj (op c.pt)) (fun i ↦ P.map (c.inj i).op))) := by
  classical
  let kanTerminal
      (L : Profinite.{u} ⥤ X.ProEt) (U : X.ProEt) (T : Profinite.{u})
      (b : ∀ S, (U ⟶ L.obj S) ≃ (T ⟶ S))
      (hb : ∀ S S' (g : S ⟶ S') (f : U ⟶ L.obj S),
        b S' (f ≫ L.map g) = b S f ≫ g) :
      IsTerminal (CostructuredArrow.mk ((b T).symm (𝟙 T)).op :
        CostructuredArrow L.op (op U)) := by
    let q := (b T).symm (𝟙 T)
    have hq : b T q = 𝟙 T := (b T).apply_symm_apply _
    refine IsTerminal.ofUniqueHom (fun s ↦
      CostructuredArrow.homMk (b s.left.unop s.hom.unop).op ?_) ?_
    · apply Quiver.Hom.unop_inj
      change q ≫ L.map (b _ s.hom.unop) = s.hom.unop
      apply (b _).injective
      rw [hb, hq, Category.id_comp]
    · intro s m
      apply CostructuredArrow.hom_ext
      apply Quiver.Hom.unop_inj
      have hm : q ≫ L.map m.left.unop = s.hom.unop :=
        congrArg Quiver.Hom.unop (CostructuredArrow.w m)
      have := congrArg (b s.left.unop) hm
      change m.left.unop = b s.left.unop s.hom.unop
      simpa only [hb, hq, Category.id_comp] using this
  -- Combine the summand equivalences using the two coproduct universal properties.
  let coproductMapEquiv
      (L : Profinite.{u} ⥤ X.ProEt)
      {I : Type u} (U : I → X.ProEt) (c : Cofan U) (hc : IsColimit c)
      (T : I → Profinite.{u}) [HasCoproduct T]
      (b : ∀ i S, (U i ⟶ L.obj S) ≃ (T i ⟶ S)) (S : Profinite.{u}) :
      (c.pt ⟶ L.obj S) ≃ (∐ T ⟶ S) := by
    exact
      { toFun := fun f ↦ Sigma.desc (fun i ↦ b i S (c.inj i ≫ f))
        invFun := fun g ↦ Cofan.IsColimit.desc hc (fun i ↦ (b i S).symm (Sigma.ι T i ≫ g))
        left_inv := fun f ↦ by
          apply Cofan.IsColimit.hom_ext hc
          intro i
          simp
        right_inv := fun g ↦ by
          apply Sigma.hom_ext
          intro i
          simp }
  have coproductMapEquiv_inj
      (L : Profinite.{u} ⥤ X.ProEt)
      {I : Type u} (U : I → X.ProEt) (c : Cofan U) (hc : IsColimit c)
      (T : I → Profinite.{u}) [HasCoproduct T]
      (b : ∀ i S, (U i ⟶ L.obj S) ≃ (T i ⟶ S)) (S : Profinite.{u})
      (f : c.pt ⟶ L.obj S) (i : I) :
      Sigma.ι T i ≫ coproductMapEquiv L U c hc T b S f = b i S (c.inj i ≫ f) := by
    exact Sigma.ι_comp_desc _ _
  have coproductMapEquiv_natural
      (L : Profinite.{u} ⥤ X.ProEt)
      {I : Type u} (U : I → X.ProEt) (c : Cofan U) (hc : IsColimit c)
      (T : I → Profinite.{u}) [HasCoproduct T]
      (b : ∀ i S, (U i ⟶ L.obj S) ≃ (T i ⟶ S))
      (hb : ∀ i S S' (g : S ⟶ S') (f : U i ⟶ L.obj S),
        b i S' (f ≫ L.map g) = b i S f ≫ g)
      (S S' : Profinite.{u}) (g : S ⟶ S') (f : c.pt ⟶ L.obj S) :
      coproductMapEquiv L U c hc T b S' (f ≫ L.map g) =
        coproductMapEquiv L U c hc T b S f ≫ g := by
    apply Sigma.hom_ext
    intro i
    simp only [coproductMapEquiv, Equiv.coe_fn_mk, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    rw [← Category.assoc, hb]
  -- Construct the coproduct in the slice using descent on the scheme coproduct.
  let f : (∐ fun i ↦ (U i).left) ⟶ X := Sigma.desc (fun i ↦ (U i).hom)
  have hf : WeaklyEtale f :=
    IsZariskiLocalAtSource.sigmaDesc (fun i ↦ (U i).prop)
  let W : X.ProEt := Scheme.ProEt.mk f
  let ι : ∀ i, U i ⟶ W := fun i ↦
    MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (U i).left) i)
      (by dsimp [W]; simp [f])
  let c : Cofan U := Cofan.mk W ι
  have hc : IsColimit c := by
    refine Cofan.IsColimit.mk c (fun t ↦
      MorphismProperty.Over.homMk (Sigma.desc (fun i ↦ (t.inj i).left)) ?_) ?_ ?_
    · change Sigma.desc (fun i ↦ (t.inj i).left) ≫ t.pt.hom = f
      apply Sigma.hom_ext
      intro i
      simp [f, ← Category.assoc]
    · intro t i
      apply MorphismProperty.Over.Hom.ext
      exact Sigma.ι_comp_desc _ _
    · intro t m hm
      apply MorphismProperty.Over.Hom.ext
      apply Sigma.hom_ext
      intro i
      have h := congrArg (fun z ↦ z.left) (hm i)
      change Sigma.ι (fun i ↦ (U i).left) i ≫ m.left = (t.inj i).left at h
      simpa using h
  -- Represent maps from each summand by its profinite component quotient.
  obtain ⟨htop, e, he, _⟩ := proEtale_point_components_maps X
  let (i : I) : CompactSpace (ConnectedComponents (U i).left) := (htop _ (ha i) (hw i)).1
  let (i : I) : T2Space (ConnectedComponents (U i).left) := (htop _ (ha i) (hw i)).2.1
  let (i : I) : TotallyDisconnectedSpace (ConnectedComponents (U i).left) :=
    (htop _ (ha i) (hw i)).2.2
  let T (i : I) : Profinite.{u} := Profinite.of (ConnectedComponents (U i).left)
  let b (i : I) (S : Profinite.{u}) :
      (U i ⟶ (profiniteToProEtOf X).obj S) ≃ (T i ⟶ S) :=
    (e (U i) (ha i) (hw i) S).trans
      { toFun := fun f ↦ ConcreteCategory.ofHom f
        invFun := fun f ↦ f.hom.hom
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  have hb (i : I) (S S' : Profinite.{u}) (g : S ⟶ S')
      (f : U i ⟶ (profiniteToProEtOf X).obj S) :
      b i S' (f ≫ (profiniteToProEtOf X).map g) = b i S f ≫ g := by
    apply ConcreteCategory.hom_injective
    exact he (U i) (ha i) (hw i) S S' g f
  -- The coproduct universal properties represent maps from W without evaluating W.
  let bW := coproductMapEquiv (profiniteToProEtOf X) U c hc T b
  have hbW := coproductMapEquiv_natural (profiniteToProEtOf X) U c hc T b hb
  have hkan (L : Profinite.{u} ⥤ X.ProEt) (U : X.ProEt) (T : Profinite.{u})
      (b : ∀ S, (U ⟶ L.obj S) ≃ (T ⟶ S))
      (hb : ∀ S S' (g : S ⟶ S') (f : U ⟶ L.obj S),
        b S' (f ≫ L.map g) = b S f ≫ g)
      (F : (Profinite.{u})ᵒᵖ ⥤ C) (P : X.ProEtᵒᵖ ⥤ C)
      (η : F ⟶ L.op ⋙ P)
      (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension) :
      ∃ e : P.obj (op U) ≅ F.obj (op T),
        ∀ (S : Profinite.{u}) (f : U ⟶ L.obj S),
          η.app (op S) ≫ P.map f.op ≫ e.hom = F.map (b S f).op := by
    let t : CostructuredArrow L.op (op U) :=
      CostructuredArrow.mk ((b T).symm (𝟙 T)).op
    let ht : IsTerminal t := kanTerminal L U T b hb
    let c := (Functor.LeftExtension.mk P η).coconeAt (op U)
    have : IsIso (c.ι.app t) := (hP (op U)).isIso_ι_app_of_isTerminal t ht
    refine ⟨(asIso (c.ι.app t)).symm, ?_⟩
    intro S f
    let s : CostructuredArrow L.op (op U) := CostructuredArrow.mk f.op
    have h := c.w (ht.from s)
    change η.app (op S) ≫ P.map f.op ≫ inv (c.ι.app t) = _
    have hm : (ht.from s).left = (b S f).op := rfl
    change F.map (ht.from s).left ≫ c.ι.app t = η.app (op S) ≫ P.map f.op at h
    rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id, hm]
  obtain ⟨eW, heW⟩ := hkan (profiniteToProEtOf X) W (∐ T) bW hbW F.obj P η hP
  have hi (i : I) := hkan (profiniteToProEtOf X) (U i) (T i) (b i) (hb i)
    F.obj P η hP
  choose ei hei using hi
  -- Kan cocone legs jointly detect the comparison with each summand restriction.
  have hcompat (i : I) : P.map (c.inj i).op ≫ (ei i).hom =
      eW.hom ≫ F.obj.map (Sigma.ι T i).op := by
    apply (hP (op W)).hom_ext'
    intro S f
    cases S with | op S =>
      change η.app (op S) ≫ P.map f ≫ (P.map (c.inj i).op ≫ (ei i).hom) =
        η.app (op S) ≫ P.map f ≫ (eW.hom ≫ F.obj.map (Sigma.ι T i).op)
      calc
        _ = η.app (op S) ≫ P.map (c.inj i ≫ f.unop).op ≫ (ei i).hom := by
          simp only [op_comp, P.map_comp, Quiver.Hom.op_unop, Category.assoc]
        _ = F.obj.map (b i S (c.inj i ≫ f.unop)).op := hei i S _
        _ = F.obj.map (bW S f.unop).op ≫ F.obj.map (Sigma.ι T i).op := by
          rw [← F.obj.map_comp, ← op_comp, coproductMapEquiv_inj]
        _ = _ := by
          have h := heW S f.unop
          change η.app (op S) ≫ P.map f ≫ eW.hom = F.obj.map (bW S f.unop).op at h
          rw [← h]
          simp only [Category.assoc]
  -- Transport the product preserved by the coherent sheaf through the evaluation isos.
  have : PreservesFiniteProducts F.obj := inferInstance
  let d := Fan.mk (F.obj.obj (op (∐ T))) (fun i ↦ F.obj.map (Sigma.ι T i).op)
  have hd : IsLimit d := isLimitFanMkObjOfIsLimit F.obj (fun i ↦ op (T i)) _
    (Cofan.IsColimit.op (coproductIsCoproduct T))
  refine ⟨c, ⟨hc⟩, ⟨?_⟩⟩
  refine Fan.IsLimit.mk _ (fun s ↦
    Fan.IsLimit.lift hd (fun i ↦ s.proj i ≫ (ei i).hom) ≫ eW.inv) ?_ ?_
  · intro s i
    apply (cancel_mono (ei i).hom).mp
    change ((Fan.IsLimit.lift hd (fun i ↦ s.proj i ≫ (ei i).hom) ≫ eW.inv) ≫
      P.map (c.inj i).op) ≫ (ei i).hom = _
    simp only [Category.assoc, hcompat, Iso.inv_hom_id_assoc]
    exact Fan.IsLimit.fac hd _ i
  · intro s m hm
    apply (cancel_mono eW.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Fan.IsLimit.hom_ext hd
    intro i
    rw [Fan.IsLimit.fac]
    change (m ≫ eW.hom) ≫ F.obj.map (Sigma.ι T i).op = _
    rw [Category.assoc, ← hcompat, ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ (ei i).hom) (hm i)

end AlgebraicGeometry.ProEtale
