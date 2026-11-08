/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonDiagonalSection
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageKanRepresentative

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The concrete diagonal unit and its unique-extension property

Source: Stacks Project, Tag 0GLZ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

-- Local notation expands the diagonal formula; the public declaration introduces
-- no second copy of the downstream `proEtaleComparisonEtaleSection` definition.
set_option quotPrecheck false in
local notation:max "δ[" X "," F "," U "]" s:max =>
  (by
    let _ : (MorphismProperty.Over.pullback @Etale ⊤ (U).hom).IsContinuous
        ((X).smallGrothendieckTopology @Etale)
        ((U).left.smallGrothendieckTopology @Etale) :=
      Scheme.isContinuous_overPullback @Etale @Etale le_rfl (U).hom
    exact ((Scheme.etaleSetPullback (U).hom).obj F).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift (𝟙 (U).left) (𝟙 (U).left) (by simp)) (by simp) :
        Scheme.Etale.mk (𝟙 (U).left) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (U).hom).obj U).op
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ (U).hom) (Type _)
        ((X).smallGrothendieckTopology @Etale)
        ((U).left.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op U) s)
  : ((Scheme.etaleSetPullback (U).hom).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 (U).left))))

-- Restrict a pro-étale sheaf to each local étale site, then transpose alpha.
private noncomputable abbrev b {S T : Scheme.{u}} (f : T ⟶ S) :=
  MorphismProperty.Over.pullback @Etale ⊤ f

private instance b_continuous {S T : Scheme.{u}} (f : T ⟶ S) :
    (b f).IsContinuous (S.smallGrothendieckTopology @Etale)
      (T.smallGrothendieckTopology @Etale) :=
  Scheme.isContinuous_overPullback @Etale @Etale le_rfl f

private noncomputable def push {S T : Scheme.{u}} (f : T ⟶ S) :=
  (b f).sheafPushforwardContinuous (Type (u + 1))
    (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)

private noncomputable def adj {S T : Scheme.{u}} (f : T ⟶ S) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (b f)
    (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)

private def localSite {X : Scheme.{u}} (Y : X.ProEt) : Y.left.Etale ⥤ X.ProEt :=
  Scheme.toProEt Y.left ⋙ MorphismProperty.Over.map ⊤ Y.prop

private instance localSite_continuous {X : Scheme.{u}} (Y : X.ProEt) :
    (localSite Y).IsContinuous Y.left.smallEtaleTopology (Scheme.ProEt.topology X) := by
  let _ : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ Y.prop).IsContinuous
      (Scheme.ProEt.topology Y.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap Y.prop
  exact Functor.isContinuous_comp (Scheme.toProEt Y.left)
    (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ Y.prop)
    Y.left.smallEtaleTopology (Scheme.ProEt.topology Y.left) (Scheme.ProEt.topology X)

private def localSheaf {X : Scheme.{u}}
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (Y : X.ProEt) :=
  ((localSite Y).sheafPushforwardContinuous (Type (u + 1))
    Y.left.smallEtaleTopology (Scheme.ProEt.topology X)).obj G

private noncomputable def projection {X : Scheme.{u}} (Y : X.ProEt) (U : X.Etale) :
    (localSite Y).obj ((b Y.hom).obj U) ⟶ (Scheme.toProEt X).obj U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom Y.hom) (by
    change pullback.fst U.hom Y.hom ≫ U.hom = pullback.snd U.hom Y.hom ≫ Y.hom
    exact pullback.condition)

private noncomputable def localAlpha {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (α : F ⟶ ((Scheme.toProEt X).sheafPushforwardContinuous
      (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G)
    (Y : X.ProEt) :
    F ⟶ (push Y.hom).obj (localSheaf G Y) := ⟨{
  app U := α.hom.app U ≫ G.obj.map (projection Y U.unop).op
  naturality := by
    intro U V g
    have h := α.hom.naturality g
    dsimp at h ⊢
    rw [reassoc_of% h]
    change α.hom.app U ≫ G.obj.map ((Scheme.toProEt X).map g.unop).op ≫
        G.obj.map (projection Y V.unop).op =
      (α.hom.app U ≫ G.obj.map (projection Y U.unop).op) ≫
        G.obj.map ((localSite Y).map ((b Y.hom).map g.unop)).op
    simp only [Category.assoc]
    rw [← G.obj.map_comp, ← G.obj.map_comp]
    congr 2
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change pullback.fst V.unop.hom Y.hom ≫ g.unop.left =
      ((b Y.hom).map g.unop).left ≫ pullback.fst U.unop.hom Y.hom
    simp [MorphismProperty.Over.pullback_map_left]
}⟩

private noncomputable def localTranspose {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (α : F ⟶ ((Scheme.toProEt X).sheafPushforwardContinuous
      (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G)
    (Y : X.ProEt) : (Scheme.etaleSetPullback Y.hom).obj F ⟶ localSheaf G Y :=
  ((adj Y.hom).homEquiv F (localSheaf G Y)).symm (localAlpha F G α Y)

-- The chosen inverse-image composition isomorphism, with its unit equation.
-- Pasting the two local adjunctions gives naturality of the extension.
private def identityIso {X : Scheme.{u}} (Y : X.ProEt) :
    (localSite Y).obj (Scheme.Etale.mk (𝟙 Y.left)) ≅ Y :=
  MorphismProperty.Over.isoMk (Iso.refl Y.left) (by
    change 𝟙 Y.left ≫ Y.hom = 𝟙 Y.left ≫ Y.hom
    rfl)

private noncomputable def sectionMap {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (α : F ⟶ ((Scheme.toProEt X).sheafPushforwardContinuous
      (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G)
    (Y : X.ProEt) :
    ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y.left))) → G.obj.obj (op Y) :=
  fun t ↦ G.obj.map (identityIso Y).inv.op
    ((localTranspose F G α Y).hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) t)

-- For uniqueness, turn local Kan representatives into diagonal restrictions.
-- Sheafification is locally surjective; the Kan extension has explicit representatives.
end AlgebraicGeometry
