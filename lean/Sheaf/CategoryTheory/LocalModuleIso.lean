/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.CategoryTheory.LocalModuleHom

/-! # Local isomorphisms of module sheaves

Source: Stacks Project, Modules on Sites, Tag 093T, inverse-pair description.
(blueprint: lem-sf-local-module-isom-sheaf).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} (M N : SheafOfModules.{u} R)

/-- Restriction of a local module isomorphism. -/
def restrictIso {U V : Cᵒᵖ} (f : U ⟶ V) (a : M.over U.unop ≅ N.over U.unop) :
    M.over V.unop ≅ N.over V.unop :=
  ((overFunctorMap R f.unop).app M).symm ≪≫ (overMap R f.unop).mapIso a ≪≫
    (overFunctorMap R f.unop).app N

/-- The presheaf of actual isomorphisms on the ringed slices. -/
def localIso : Cᵒᵖ ⥤ Type u where
  obj U := M.over U.unop ≅ N.over U.unop
  map f := ↾(restrictIso M N f)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Iso.ext
    ext V x
    change a.hom.val.app (op ((Over.map (𝟙 U).unop).obj V.unop)) x = a.hom.val.app V x
    have h := ConcreteCategory.congr_hom
      ((presheafHom M.val.presheaf N.val.presheaf).map_id U)
      ((localHomEquiv M N U).symm a.hom).val
    exact ConcreteCategory.congr_hom (congr_app h V) x
  map_comp {U V W} f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Iso.ext
    ext T x
    change a.hom.val.app (op ((Over.map (f ≫ g).unop).obj T.unop)) x =
      a.hom.val.app (op ((Over.map f.unop).obj ((Over.map g.unop).obj T.unop))) x
    have h := ConcreteCategory.congr_hom
      ((presheafHom M.val.presheaf N.val.presheaf).map_comp f g)
      ((localHomEquiv M N U).symm a.hom).val
    exact ConcreteCategory.congr_hom (congr_app h T) x

/-- Forget the inverse of a local isomorphism. -/
def localIsoHom : localIso M N ⟶ localHom M N where
  app U := ↾fun a ↦ (localHomEquiv M N U).symm a.hom
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    ext x
    rfl

/-- Take the inverse as a local module morphism. -/
def localIsoInv : localIso M N ⟶ localHom N M where
  app U := ↾fun a ↦ (localHomEquiv N M U).symm a.inv
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    ext x
    rfl

/-- Local isomorphisms glue, together with their inverses. -/
theorem localIso_isSheaf : Presheaf.IsSheaf J (localIso M N) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U S hS x hx
  let H := (isSheaf_iff_isSheaf_of_type J _).1 (localHom_isSheaf M N)
  let H' := (isSheaf_iff_isSheaf_of_type J _).1 (localHom_isSheaf N M)
  let a := (H S hS).amalgamate (x.map (localIsoHom M N)) (hx.map _)
  let b := (H' S hS).amalgamate (x.map (localIsoInv M N)) (hx.map _)
  have ha (V : C) (f : V ⟶ U) (hf : S f) :
      (localHom M N).map f.op a = (localHomEquiv M N (op V)).symm (x f hf).hom :=
    (H S hS).valid_glue (hx.map _) f hf
  have hb (V : C) (f : V ⟶ U) (hf : S f) :
      (localHom N M).map f.op b = (localHomEquiv N M (op V)).symm (x f hf).inv :=
    (H' S hS).valid_glue (hx.map _) f hf
  have hab : localHomComp M N M a b = localHomId M (op U) := by
    apply (((isSheaf_iff_isSheaf_of_type J _).1 (localHom_isSheaf M M)).isSeparated S hS).ext
    intro V f hf
    rw [localHomComp_map, localHomId_map, ha V f hf, hb V f hf]
    apply (localHomEquiv M M (op V)).injective
    simp [localHomComp, localHomId]
  have hba : localHomComp N M N b a = localHomId N (op U) := by
    apply (((isSheaf_iff_isSheaf_of_type J _).1 (localHom_isSheaf N N)).isSeparated S hS).ext
    intro V f hf
    rw [localHomComp_map, localHomId_map, ha V f hf, hb V f hf]
    apply (localHomEquiv N N (op V)).injective
    simp [localHomComp, localHomId]
  let e : M.over U ≅ N.over U :=
    { hom := localHomEquiv M N (op U) a
      inv := localHomEquiv N M (op U) b
      hom_inv_id := by
        simpa [localHomComp, localHomId] using congrArg (localHomEquiv M M (op U)) hab
      inv_hom_id := by
        simpa [localHomComp, localHomId] using congrArg (localHomEquiv N N (op U)) hba }
  refine ⟨e, ?_, ?_⟩
  · intro V f hf
    apply Iso.ext
    apply (localHomEquiv M N (op V)).symm.injective
    exact ha V f hf
  · intro e' he'
    apply Iso.ext
    apply (localHomEquiv M N (op U)).symm.injective
    apply (H.isSeparated S hS).ext
    intro V f hf
    have he := congrArg (fun z ↦ (localHomEquiv M N (op V)).symm z.hom) (he' f hf)
    exact he.trans (ha V f hf).symm

end SheafOfModules
