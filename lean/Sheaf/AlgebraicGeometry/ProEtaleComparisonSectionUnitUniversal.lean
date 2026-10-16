/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.AlgebraicGeometry.EtaleSetTerminalTransport
import Sheaf.AlgebraicGeometry.ProEtaleComparisonDiagonalSection
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

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

set_option backward.isDefEq.respectTransparency false in
/-- The comparison unit is constructed section by section, by pulling back
along the diagonal and decoding with e. Source: Stacks Project, Tag 0GLZ.
(blueprint: def-cbc-comparison-section-diagonal-unit).
Naturality in site objects follows from diagonal-section naturality and hres;
naturality in coefficients follows from hfun and naturality of the inverse-image unit. -/
noncomputable def proEtaleComparisonSectionUnit (X : Scheme.{u})
    (A : Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (e : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt),
      (A.obj F).obj.obj (op Y) ≃
        ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 Y.left))))
    (hres : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (Y Z : X.ProEt) (g : Z ⟶ Y) (s : (A.obj F).obj.obj (op Y)),
      e F Z ((A.obj F).obj.map g.op s) =
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
            (Y.left.smallGrothendieckTopology @Etale)
            (Z.left.smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
                (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
            (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv) (e F Y s))
    (hfun : ∀ (F F' : Sheaf X.smallEtaleTopology (Type (u + 1))) (ψ : F ⟶ F')
      (Y : X.ProEt) (s : (A.obj F).obj.obj (op Y)),
      e F' Y ((A.map ψ).hom.app (op Y) s) =
        ((Scheme.etaleSetPullback Y.hom).map ψ).hom.app
          (op (Scheme.Etale.mk (𝟙 Y.left))) (e F Y s)) :
    𝟭 (Sheaf X.smallEtaleTopology (Type (u + 1))) ⟶
      A ⋙ (Scheme.toProEt X).sheafPushforwardContinuous
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X) where
  app F := ⟨{
    app U := by
      dsimp only [Functor.id_obj, Functor.comp_obj]
      simpa only [Functor.sheafPushforwardContinuous_obj_obj_obj] using
        (↾fun s ↦ (e F ((Scheme.toProEt X).obj U.unop)).symm
          (δ[X, F, U.unop] s))
    naturality := by
      intro U V g
      apply ConcreteCategory.hom_ext
      intro s
      apply (e F ((Scheme.toProEt X).obj V.unop)).injective
      dsimp
      simp only [Functor.sheafPushforwardContinuous_obj_obj_map]
      erw [hres F ((Scheme.toProEt X).obj U.unop)
        ((Scheme.toProEt X).obj V.unop) ((Scheme.toProEt X).map g.unop)]
      simp only [Equiv.apply_symm_apply]
      exact proEtaleComparisonDiagonalSection_naturality F U.unop V.unop g.unop s
  }⟩
  naturality := by
    intro F F' ψ
    ext U s
    apply (e F' ((Scheme.toProEt X).obj U.unop)).injective
    dsimp
    simp only [Functor.sheafPushforwardContinuous_map_hom_app]
    erw [hfun F F' ψ ((Scheme.toProEt X).obj U.unop)]
    simp only [Equiv.apply_symm_apply]
    let _ : (MorphismProperty.Over.pullback @Etale ⊤ U.unop.hom).IsContinuous
        (X.smallGrothendieckTopology @Etale)
        (U.unop.left.smallGrothendieckTopology @Etale) :=
      Scheme.isContinuous_overPullback @Etale @Etale le_rfl U.unop.hom
    have hu := ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun k ↦ k.hom)
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ U.unop.hom) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale)
          (U.unop.left.smallGrothendieckTopology @Etale)).unit.naturality ψ)) U) s
    have hn := (((Scheme.etaleSetPullback U.unop.hom).map ψ).hom.naturality
      (MorphismProperty.Over.homMk
        (pullback.lift (𝟙 U.unop.left) (𝟙 U.unop.left) (by simp)) (by simp) :
        Scheme.Etale.mk (𝟙 U.unop.left) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ U.unop.hom).obj U.unop).op)
    exact (congrArg (((Scheme.etaleSetPullback U.unop.hom).obj F').obj.map _) hu).trans
      (ConcreteCategory.congr_hom hn
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ U.unop.hom) (Type (u + 1))
            (X.smallGrothendieckTopology @Etale)
            (U.unop.left.smallGrothendieckTopology @Etale)).unit.app F).hom.app U s)).symm

/-- Precomposition with the concrete diagonal unit is bijective on morphisms.
This is a unique-extension statement about an already constructed map, without
asserting an adjunction or any natural hom-set equivalence.

Source: Stacks Project, Tag 0GLZ, the sectionwise transpose and verification of
its two inverse composites.
(blueprint: lem-cbc-comparison-section-unit-universal).
Proof: fix F, G and a morphism alpha from F to the restriction of G. For each
pro-étale Y over X, restrict G to the étale site of Y by viewing an étale
Y-scheme as a pro-étale X-scheme. This is a sheaf since étale covering families
are pro-étale covering families. For each étale U over X, restrict alpha_U along
Y times_X U to obtain F -> (Y.hom)_* G_Y. Transpose using the étale
inverse-image adjunction, evaluate at the identity of Y, and precompose with
e_F,Y to obtain beta_Y. For Z -> Y the composition-unit identity identifies
the two successive transposes: both send a section to alpha_U of that section
restricted to Z times_X U. The law hres therefore makes the beta_Y a sheaf
morphism beta:A(F)->G. On an étale U, the inverse-image/restriction
isomorphism and its unit equation show that beta applied to the diagonal
section is alpha_U. Thus beta extends alpha, proving surjectivity. For
uniqueness fix any beta with this diagonal restriction. On every étale V over
Y its components, decoded by the étale inverse-image/restriction isomorphism,
define a map (Y.hom)^*F -> G_Y. Naturality of beta for Y times_X U -> U and
the diagonal formula identify its adjoint transpose with the map used above.
Injectivity of the étale adjunction hom equivalence forces it to be the same
map; evaluating at the identity of Y gives the same beta_Y. This proves
injectivity. These arguments use equality of morphisms and apply also to
empty schemes and empty section sets. -/
theorem proEtaleComparisonSectionUnit_bijective (X : Scheme.{u})
    (A : Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (e : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt),
      (A.obj F).obj.obj (op Y) ≃
        ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 Y.left))))
    (hres : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (Y Z : X.ProEt) (g : Z ⟶ Y) (s : (A.obj F).obj.obj (op Y)),
      e F Z ((A.obj F).obj.map g.op s) =
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
            (Y.left.smallGrothendieckTopology @Etale)
            (Z.left.smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
                (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
            (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv) (e F Y s))
    (hfun : ∀ (F F' : Sheaf X.smallEtaleTopology (Type (u + 1))) (ψ : F ⟶ F')
      (Y : X.ProEt) (s : (A.obj F).obj.obj (op Y)),
      e F' Y ((A.map ψ).hom.app (op Y) s) =
        ((Scheme.etaleSetPullback Y.hom).map ψ).hom.app
          (op (Scheme.Etale.mk (𝟙 Y.left))) (e F Y s))
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) :
    Function.Bijective (fun f : A.obj F ⟶ G ↦
      (proEtaleComparisonSectionUnit X A e hres hfun).app F ≫
        ((Scheme.toProEt X).sheafPushforwardContinuous
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).map f) := by
  sorry

end AlgebraicGeometry
