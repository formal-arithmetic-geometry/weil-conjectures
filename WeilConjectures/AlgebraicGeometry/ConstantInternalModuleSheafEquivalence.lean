/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence

/-! # Encoding internal modules over a constant ring sheaf

Source: Bhatt--Scholze, Section 5.3, and Stacks Project, Tag 093I;
the tensor and sheafification encoding argument is expanded below
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory

namespace ConstantInternalModuleSheafEncoding

section PresheafEncoding

variable {C : Type u} [Category.{v} C] (R : Type w) [Ring R]

local instance evaluationMonoidal (U : C) : ((evaluation C Ab.{w}).obj U).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

noncomputable def presheafToFunctor : CategoryTheory.Mod (C ⥤ Ab.{w}) (A (C := C) R) ⥤
    (C ⥤ CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R)) where
  obj M :=
    { obj U := (((evaluation C Ab.{w}).obj U).mapMod (A (C := C) R)).obj M
      map f := CategoryTheory.Mod.homMk (M.X.map f) (by
        exact ((CategoryTheory.Mod.act (A := A (C := C) R) M.X).naturality f).symm)
      map_id U := CategoryTheory.Mod.hom_ext _ _ (M.X.map_id U)
      map_comp f g := CategoryTheory.Mod.hom_ext _ _ (M.X.map_comp f g) }
  map φ :=
    { app U := CategoryTheory.Mod.homMk (φ.hom.app U) (by
        exact congr_app (CategoryTheory.Mod.act_hom φ) U)
      naturality _ _ f := CategoryTheory.Mod.hom_ext _ _ (φ.hom.naturality f) }
  map_id M := by ext U; rfl
  map_comp φ ψ := by ext U; rfl

end PresheafEncoding

section ModuleLocalization

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (A : Cᵒᵖ ⥤ Ab.{w}) [MonObj A]

noncomputable abbrev moduleLocalizationRight :=
  (sheafificationAdjunction J Ab.{w}).modRight
    ((sheafificationAdjunction J Ab.{w}).unit.app A)

end ModuleLocalization

section SheafEncoding

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
  (R : Type w) [Ring R]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

noncomputable def modulePresheafEncoding
    (G : CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R) ⥤ ModuleCat.{w} R) :=
  presheafToFunctor (C := Cᵒᵖ) R ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj G

lemma modulePresheafEncoding_forget
    (G : CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R) ⥤ ModuleCat.{w} R)
    (hG : G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = CategoryTheory.Mod.forget (AddCommGrpCat.of R)) :
    modulePresheafEncoding (C := C) R G ⋙
      (Functor.whiskeringRight Cᵒᵖ _ _).obj (forget₂ (ModuleCat.{w} R) Ab.{w}) =
        CategoryTheory.Mod.forget (A (C := Cᵒᵖ) R) := by
  change presheafToFunctor R ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w}) = _
  rw [hG]
  rfl

noncomputable def sheafEncoding
    (G : CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R) ⥤ ModuleCat.{w} R)
    (hG : G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = CategoryTheory.Mod.forget (AddCommGrpCat.of R))
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
    [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})] :
    CategoryTheory.Mod (Sheaf J Ab.{w}) ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)) ⥤
      Sheaf J (ModuleCat.{w} R) where
  obj N := by
    let P := modulePresheafEncoding (C := C) R G
    let Q := moduleLocalizationRight J (A (C := Cᵒᵖ) R)
    refine ⟨P.obj (Q.obj N), ?_⟩
    apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ (ModuleCat.{w} R) Ab.{w})
    have h := congrArg (fun F ↦ F.obj (Q.obj N)) (modulePresheafEncoding_forget (C := C) R G hG)
    change (P.obj (Q.obj N)) ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = N.X.obj at h
    rw [h]
    exact N.X.property
  map φ := ⟨(modulePresheafEncoding (C := C) R G).map
    ((moduleLocalizationRight J (A (C := Cᵒᵖ) R)).map φ)⟩
  map_id N := by
    apply (sheafToPresheaf J (ModuleCat.{w} R)).map_injective
    exact ((moduleLocalizationRight J (A (C := Cᵒᵖ) R) ⋙
      modulePresheafEncoding (C := C) R G).map_id N)
  map_comp φ ψ := by
    apply (sheafToPresheaf J (ModuleCat.{w} R)).map_injective
    exact ((moduleLocalizationRight J (A (C := Cᵒᵖ) R) ⋙
      modulePresheafEncoding (C := C) R G).map_comp φ ψ)

variable (G : CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R) ⥤ ModuleCat.{w} R) [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = CategoryTheory.Mod.forget (AddCommGrpCat.of R))
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
    [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]

end SheafEncoding

end ConstantInternalModuleSheafEncoding

section SheafEncoding

open ConstantInternalModuleSheafEncoding

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
  (R : Type w) [Ring R]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
  [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

end SheafEncoding

end CategoryTheory
