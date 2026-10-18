/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!

# The composition isomorphism of pushforwards of sheaves is monoidal

For continuous functors `F : C ⥤ D`, `G : D ⥤ E` and an isomorphism `e : F ⋙ G ≅ FG`, the
composition isomorphism `G_* ⋙ F_* ≅ FG_*` of pushforwards of sheaves
(`CategoryTheory.Functor.sheafPushforwardContinuousComp'`) is a monoidal natural isomorphism,
for the lax monoidal structures of
`CategoryTheory.Functor.sheafPushforwardContinuousLaxMonoidal`
(`CategoryTheory.Functor.isMonoidal_sheafPushforwardContinuousComp'_hom`).

The unit part is `CategoryTheory.Functor.ε_sheafPushforwardContinuous_of_iso_comp`. For the
tensor part, a morphism of sheaves out of `P ⊗ Q` is determined by its composite with the
tensor comparison `μ` of `sheafToPresheaf` (`CategoryTheory.Sheaf.hom_ext_of_μ_comp`), and on
underlying presheaves the tensor comparison of a pushforward is the restriction of the one of
`sheafToPresheaf`
(`CategoryTheory.Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app`).

-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace Sheaf

variable {C : Type*} [Category C] {A : Type*} [Category A] [MonoidalCategory A]
  {J : GrothendieckTopology C} [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory

/-- Two morphisms of sheaves out of a tensor product `P ⊗ Q` agree as soon as they agree on
underlying presheaves after the tensor comparison `μ` of the lax monoidal functor
`sheafToPresheaf`. -/
lemma hom_ext_of_μ_comp {P Q G : Sheaf J A} {a b : P ⊗ Q ⟶ G}
    (h : μ (sheafToPresheaf J A) P Q ≫ (sheafToPresheaf J A).map a =
      μ (sheafToPresheaf J A) P Q ≫ (sheafToPresheaf J A).map b) : a = b := by
  have e (c : P ⊗ Q ⟶ G) : ((sheafificationAdjunction J A).homEquiv _ _).symm
      (μ (sheafToPresheaf J A) P Q ≫ (sheafToPresheaf J A).map c) =
        (δ (presheafToSheaf J A) _ _ ≫ ((sheafificationAdjunction J A).counit.app P ⊗ₘ
          (sheafificationAdjunction J A).counit.app Q)) ≫ c := by
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      Adjunction.counit_naturality, ← Category.assoc,
      Adjunction.map_μ_comp_counit_app_tensor]
  rw [← cancel_epi (δ (presheafToSheaf J A) _ _ ≫
    ((sheafificationAdjunction J A).counit.app P ⊗ₘ
      (sheafificationAdjunction J A).counit.app Q)), ← e, ← e, h]

end Sheaf

namespace Functor

variable {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
  (A : Type*) [Category A] [MonoidalCategory A] [BraidedCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [F.IsContinuous J K]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]

attribute [local instance] Sheaf.monoidalCategory

/-- The tensor comparison `μ` of the lax monoidal pushforward `F_*` of sheaves, read on
underlying presheaves after the tensor comparison of `sheafToPresheaf`, is the restriction
along `F.op` of the tensor comparison of `sheafToPresheaf`. -/
lemma μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous (P Q : Sheaf K A) :
    μ (sheafToPresheaf J A) ((F.sheafPushforwardContinuous A J K).obj P)
        ((F.sheafPushforwardContinuous A J K).obj Q) ≫
      (sheafToPresheaf J A).map (μ (F.sheafPushforwardContinuous A J K) P Q) =
      μ ((whiskeringLeft _ _ A).obj F.op) P.obj Q.obj ≫
        ((whiskeringLeft _ _ A).obj F.op).map (μ (sheafToPresheaf K A) P Q) := by
  have h := NatTrans.IsMonoidal.tensor
    (τ := (sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F A J K).hom) P Q
  rw [sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
    sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
    sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app, comp_μ, comp_μ] at h
  simpa using h.symm

/-- The componentwise form of
`CategoryTheory.Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous`. -/
@[reassoc]
lemma μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app (P Q : Sheaf K A)
    (U : Cᵒᵖ) :
    (μ (sheafToPresheaf J A) ((F.sheafPushforwardContinuous A J K).obj P)
        ((F.sheafPushforwardContinuous A J K).obj Q)).app U ≫
      (μ (F.sheafPushforwardContinuous A J K) P Q).hom.app U =
      (μ (sheafToPresheaf K A) P Q).app (F.op.obj U) := by
  have h := congr_app (μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous F A J K P Q) U
  exact h.trans (Category.id_comp _)

variable {F} {E : Type*} [Category E] (L : GrothendieckTopology E) [(L.W (A := A)).IsMonoidal]
  [HasWeakSheafify L A] {G : D ⥤ E} {FG : C ⥤ E} (e : F ⋙ G ≅ FG) [G.IsContinuous K L]
  [FG.IsContinuous J L]

/-- The composition isomorphism `G_* ⋙ F_* ≅ FG_*` of pushforwards of sheaves is monoidal. -/
instance isMonoidal_sheafPushforwardContinuousComp'_hom :
    NatTrans.IsMonoidal (sheafPushforwardContinuousComp' e A J K L).hom where
  unit := by
    rw [comp_ε, ε_sheafPushforwardContinuous_of_iso_comp A J K L e, Category.assoc]
  tensor P Q := by
    apply Sheaf.hom_ext_of_μ_comp
    rw [Functor.map_comp, Functor.map_comp, ← μ_natural_assoc,
      μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous FG A J L]
    refine NatTrans.ext (funext fun U ↦ ?_)
    simp only [comp_obj, ObjectProperty.ι_obj, comp_μ,
      ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
      NatTrans.comp_app, sheafPushforwardContinuous_map_hom_app,
      sheafPushforwardContinuousComp'_hom_app_hom_app, whiskeringLeft_obj_obj,
      whiskeringLeft_obj_map, Monoidal.tensorHom_app, op_obj, Monoidal.whiskeringLeft_μ_app,
      whiskerLeft_app]
    rw [μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc]
    erw [μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc]
    refine ((μ (sheafToPresheaf L A) P Q).naturality (e.inv.app U.unop).op).symm.trans ?_
    erw [Category.id_comp]
    rfl

end Functor

end CategoryTheory
