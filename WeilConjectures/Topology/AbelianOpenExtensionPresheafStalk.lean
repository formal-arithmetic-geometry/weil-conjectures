/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import Mathlib.Geometry.RingedSpace.Stalks

/-! # Interior stalk comparison before sheafification

## References

* Stacks Project, Tags 00A4 and 00A5.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

open Classical in
/-- The direct-sum extension presheaf has the original stalk at an interior point. -/
theorem abelianOpenExtensionPresheaf_stalk (X : TopCat.{w}) (U : Opens X)
    (x : U) (G : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U)) :
    ∃ e : TopCat.Presheaf.stalk G.obj x ≅
        TopCat.Presheaf.stalk ((abelianOpenExtensionPresheaf U).obj G) x.val,
      ∀ (V : Opens X) (hV : V ≤ U) (hx : x.val ∈ V),
        TopCat.Presheaf.germ G.obj ((Opens.map U.inclusion').obj V) x hx ≫ e.hom =
          AddCommGrpCat.ofHom (DirectSum.of
            (fun φ : V ⟶ U ↦ (openSlicePresheaf U G.obj).obj (op (Over.mk φ)))
            (homOfLE hV)) ≫
          TopCat.Presheaf.germ ((abelianOpenExtensionPresheaf U).obj G) V x.val hx := by
  classical
  change CategoryTheory.Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
    AddCommGrpCat.{w} at G
  let _ : ∀ (V : Opens X), DecidableEq (V ⟶ U) :=
    fun _ a b ↦ Classical.propDecidable (a = b)
  let P := (abelianOpenExtensionPresheaf U).obj G
  let Q := (U.isOpenEmbedding.functor ⋙ Opens.map U.inclusion').op ⋙ G.obj
  have himage (W : Opens U) : U.isOpenEmbedding.functor.obj W ≤ U := by
    rintro y ⟨z, hz, rfl⟩
    exact z.property
  let η : Q ⟶ U.isOpenEmbedding.functor.op ⋙ P :=
    { app := fun W ↦ AddCommGrpCat.ofHom (DirectSum.of
        (fun φ : U.isOpenEmbedding.functor.obj W.unop ⟶ U ↦
          (openSlicePresheaf U G.obj).obj (op (Over.mk φ))) (homOfLE (himage W.unop)))
      naturality := by
        intro W Z f
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        dsimp [Q, P, abelianOpenExtensionPresheaf, siteExtensionByZeroPresheaf,
          siteExtensionByZeroPresheafObj, siteExtensionByZeroRestrict, openSlicePresheaf]
        let : DecidableEq (U.isOpenEmbedding.functor.obj W.unop ⟶ U) :=
          fun a b ↦ Classical.propDecidable (a = b)
        erw [DirectSum.toAddMonoid_of]
        dsimp only [AddMonoidHom.comp_apply]
        congr 1 }
  have hi (W : (Opens U)ᵒᵖ) : IsIso (η.app W) := by
    let V := U.isOpenEmbedding.functor.obj W.unop
    let M := G.obj.obj (op ((Opens.map U.inclusion').obj V))
    let : Unique (V ⟶ U) := ⟨⟨homOfLE (himage W.unop)⟩, fun _ ↦ Subsingleton.elim _ _⟩
    have he : η.app W = (DirectSum.id M (V ⟶ U)).symm.toAddCommGrpIso.hom := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      change (DirectSum.of (fun _ : V ⟶ U ↦ M) (homOfLE (himage W.unop))) s =
        (DirectSum.id M (V ⟶ U)).symm s
      rw [DirectSum.id_symm_apply]
      ext i
      simp [Subsingleton.elim (homOfLE (himage W.unop)) i,
        Subsingleton.elim (default : V ⟶ U) i]
    rw [he]
    infer_instance
  let τ : U.isOpenEmbedding.functor ⋙ Opens.map U.inclusion' ≅ 𝟭 (Opens U) :=
    NatIso.ofComponents (fun W ↦ eqToIso (Opens.map_functor_eq W))
      (fun _ ↦ Subsingleton.elim _ _)
  let q : Q ≅ G.obj := Functor.isoWhiskerRight (NatIso.op τ).symm G.obj ≪≫ Functor.leftUnitor G.obj
  have : IsIso η := NatIso.isIso_of_isIso_app η
  let S : AlgebraicGeometry.PresheafedSpace AddCommGrpCat.{w} := ⟨X, P⟩
  let e : TopCat.Presheaf.stalk G.obj x ≅ P.stalk x.val :=
    (TopCat.Presheaf.stalkFunctor (X := (Opens.toTopCat X).obj U)
      AddCommGrpCat.{w} x).mapIso
      (q.symm ≪≫ asIso η) ≪≫ S.restrictStalkIso U.isOpenEmbedding x
  refine ⟨e, ?_⟩
  intro V hV hx
  dsimp [e]
  erw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  simp only [Category.assoc]
  erw [S.restrictStalkIso_hom_eq_germ U.isOpenEmbedding
    ((Opens.map U.inclusion').obj V) x hx]
  dsimp [q, τ, η, NatIso.op, NatTrans.op]
  simp only [eqToHom_op, eqToHom_map, Category.id_comp]
  dsimp only [openSlicePresheaf, Functor.comp_obj, Functor.op_obj, Over.forget_obj]
  dsimp only [S, Over.mk]
  have hg (W V : Opens X) (h : W = V) (hW : W ≤ U) (hV : V ≤ U)
      (hxW : x.val ∈ W) (hxV : x.val ∈ V) :
      (eqToHom (congrArg (fun A : Opens X ↦
          G.obj.obj (op ((Opens.map U.inclusion').obj A))) h.symm) ≫
        AddCommGrpCat.ofHom (DirectSum.of
          (fun _ : W ⟶ U ↦ G.obj.obj (op ((Opens.map U.inclusion').obj W)))
          (homOfLE hW))) ≫ P.germ W x.val hxW =
        AddCommGrpCat.ofHom (DirectSum.of
          (fun _ : V ⟶ U ↦ G.obj.obj (op ((Opens.map U.inclusion').obj V)))
          (homOfLE hV)) ≫ P.germ V x.val hxV := by
    subst V
    exact congrArg (fun f ↦ f ≫ P.germ W x.val hxW) (Category.id_comp _)
  exact hg _ V (openImage_preimage_eq U V hV) _ hV _ hx

end TopCat.Sheaf
