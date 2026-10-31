/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-! # Extending module objects from a dense subsite

Source: Stacks Project, Sites, Tag 03A0 (comparison); Modules on Sites,
equivalences of ringed topoi (blueprint: lem-sfb-dense-subsite-module-extension).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uC uD vC vD

open CategoryTheory Opposite

namespace SheafOfModules

private def denseRestriction {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (F : C ⥤ D) [F.IsContinuous J K]
    (R : Sheaf K RingCat.{u}) :=
  pushforward.{u} (F := F) (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R))

private def extendHom {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (F : C ⥤ D) [F.IsContinuous J K]
    [F.IsCoverDense K] [F.IsLocallyFull K] (R : Sheaf K RingCat.{u})
    {M N : SheafOfModules.{u} R}
    (f : (denseRestriction (J := J) F R).obj M ⟶
      (denseRestriction (J := J) F R).obj N) : M ⟶ N := by
  let a : F.op ⋙ M.val.presheaf ⟶ F.op ⋙ N.val.presheaf :=
    (PresheafOfModules.toPresheaf.{u} _).map f.val
  let e := Functor.IsCoverDense.restrictHomEquivHom (G := F)
    (ℱ := M.val.presheaf) (ℱ' := (toSheaf.{u} _).obj N)
  let b : M.val.presheaf ⟶ N.val.presheaf := e a
  have hb (U : C) : b.app (op (F.obj U)) = a.app (op U) :=
    congrArg (fun t ↦ t.app (op U)) (e.symm_apply_apply a)
  refine ⟨PresheafOfModules.homMk b ?_⟩
  intro U r m
  apply Functor.IsCoverDense.ext F
    ((sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
      ((toSheaf.{u} _).obj N)) U.unop
  intro V g
  change N.val.map g.op ((b.app U).hom (r • m)) =
    N.val.map g.op (r • (b.app U).hom m)
  have hn (z : M.val.obj U) :
      (b.app (op (F.obj V))).hom (M.val.map g.op z) =
        N.val.map g.op ((b.app U).hom z) := CategoryTheory.congr_fun (b.naturality g.op) z
  rw [← hn, M.val.map_smul, hb, N.val.map_smul, ← hn, hb]
  exact (f.val.app (op V)).hom.map_smul _ _

private lemma extendHom_restrict {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (F : C ⥤ D) [F.IsContinuous J K]
    [F.IsCoverDense K] [F.IsLocallyFull K] (R : Sheaf K RingCat.{u})
    {M N : SheafOfModules.{u} R}
    (f : (denseRestriction (J := J) F R).obj M ⟶ (denseRestriction (J := J) F R).obj N) :
    (denseRestriction (J := J) F R).map (extendHom (J := J) F R f) = f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  let a := (PresheafOfModules.toPresheaf.{u} _).map f.val
  let e := Functor.IsCoverDense.restrictHomEquivHom (G := F)
    (ℱ := M.val.presheaf) (ℱ' := (toSheaf.{u} _).obj N)
  exact congrArg (fun t ↦ (t.app U).hom m) (e.symm_apply_apply a)

private lemma restrictHom_injective {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (F : C ⥤ D) [F.IsContinuous J K]
    [F.IsCoverDense K] [F.IsLocallyFull K] (R : Sheaf K RingCat.{u})
    {M N : SheafOfModules.{u} R} {f g : M ⟶ N}
    (h : (denseRestriction (J := J) F R).map f =
      (denseRestriction (J := J) F R).map g) : f = g := by
  apply (toSheaf.{u} R).map_injective
  apply Sheaf.hom_ext
  apply (Functor.IsCoverDense.restrictHomEquivHom (G := F)
    (ℱ := M.val.presheaf) (ℱ' := (toSheaf.{u} _).obj N)).symm.injective
  exact congrArg (fun t ↦ (PresheafOfModules.toPresheaf.{u} _).map t.val) h

/-- Essential surjectivity of module restriction follows from additive sheaf comparison.

Source: Stacks Project, Sites, Tag 03A0; Modules on Sites, equivalences of ringed topoi
(blueprint: lem-sfb-dense-subsite-module-extension).

Proof: extend the underlying additive sheaf using the given equivalence. On the dense
subcategory, transport the scalar action through its counit. The comparison lemma for
maps into a sheaf extends this action to the product of the ring and additive presheaves.
A section is determined by its restrictions to the dense subcategory. Embed each section
group into the product of the restricted module groups; the extended action commutes with
this embedding. Injectivity therefore transfers all module axioms. The action is natural
by construction, so the additive sheaf becomes a module sheaf. The counit is linear on
every object of the dense subcategory and gives the required module isomorphism. -/
private theorem denseRestriction_essSurj
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} (F : C ⥤ D)
    [F.IsDenseSubsite J K]
    [(F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).IsEquivalence]
    (R : Sheaf K RingCat.{u}) :
    (pushforward.{u} (F := F)
      (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R))).EssSurj := by
  classical
  have := Functor.IsDenseSubsite.isCoverDense J K F
  have := Functor.IsDenseSubsite.isLocallyFull J K F
  let S := (F.sheafPushforwardContinuous RingCat.{u} J K).obj R
  let E := (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).asEquivalence
  refine ⟨fun M ↦ ?_⟩
  let N := E.inverse.obj ((toSheaf S).obj M)
  let i : F.op ⋙ N.obj ≅ M.val.presheaf :=
    (sheafToPresheaf J AddCommGrpCat.{u}).mapIso (E.counitIso.app ((toSheaf S).obj M))
  let modM (U : Cᵒᵖ) : Module (R.obj.obj (F.op.obj U)) (M.val.presheaf.obj U) :=
    inferInstanceAs (Module (S.obj.obj U) (M.val.obj U))
  let modM' (V : C) : Module (R.obj.obj (op (F.obj V)))
      (M.val.presheaf.obj (op V)) :=
    inferInstanceAs (Module (S.obj.obj (op V)) (M.val.obj (op V)))
  let P : Dᵒᵖ ⥤ Type u :=
    { obj := fun U ↦ (R.obj.obj U) × (N.obj.obj U)
      map := fun g ↦ TypeCat.ofHom fun p ↦ (R.obj.map g p.1, N.obj.map g p.2)
      map_id := by intro U; ext p <;> simp
      map_comp := by intro U V W f g; ext p <;> simp }
  let Q := (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj N
  let a : F.op ⋙ P ⟶ F.op ⋙ Q.obj :=
    { app := fun U ↦ TypeCat.ofHom fun p ↦ (i.inv.app U).hom (p.1 • (i.hom.app U).hom p.2)
      naturality := by
        intro U V g
        ext p
        have hi (n : N.obj.obj (F.op.obj U)) :
            (i.hom.app V).hom (N.obj.map (F.op.map g) n) = M.val.map g ((i.hom.app U).hom n) :=
          CategoryTheory.congr_fun (i.hom.naturality g) n
        have hj (m : M.val.obj U) :
            (i.inv.app V).hom (M.val.map g m) = N.obj.map (F.op.map g) ((i.inv.app U).hom m) :=
          CategoryTheory.congr_fun (i.inv.naturality g) m
        change (i.inv.app V).hom (R.obj.map (F.op.map g) p.1 •
          (i.hom.app V).hom (N.obj.map (F.op.map g) p.2)) =
            N.obj.map (F.op.map g) ((i.inv.app U).hom (p.1 • (i.hom.app U).hom p.2))
        rw [hi]
        exact (congrArg (i.inv.app V).hom
          (M.val.map_smul g p.1 ((i.hom.app U).hom p.2)).symm).trans (hj _) }
  let e := Functor.IsCoverDense.restrictHomEquivHom (G := F) (ℱ := P) (ℱ' := Q)
  let b := e a
  have hb (V : C) : b.app (op (F.obj V)) = a.app (op V) :=
    congrArg (fun t ↦ t.app (op V)) (e.symm_apply_apply a)
  have hact (U : Cᵒᵖ) (r : R.obj.obj (F.op.obj U))
      (n : N.obj.obj (F.op.obj U)) :
      (i.hom.app U).hom (b.app (F.op.obj U) (r, n)) = r • (i.hom.app U).hom n := by
    exact (congrArg (fun t ↦ (i.hom.app U).hom ((t.app U) (r, n)))
      (e.symm_apply_apply a)).trans (CategoryTheory.congr_fun (i.inv_hom_id_app U) _)
  have hres (U : Dᵒᵖ) (V : C) (g : F.obj V ⟶ U.unop)
      (r : R.obj.obj U) (n : N.obj.obj U) :
      (i.hom.app (op V)).hom (N.obj.map g.op (b.app U (r, n))) =
        R.obj.map g.op r • (i.hom.app (op V)).hom (N.obj.map g.op n) := by
    have hn : b.app (op (F.obj V)) (R.obj.map g.op r, N.obj.map g.op n) =
        N.obj.map g.op (b.app U (r, n)) := by
      exact congrArg (fun h : P.obj U ⟶ Q.obj.obj (op (F.obj V)) ↦ h (r, n))
        (b.naturality g.op)
    rw [← hn, hb]
    exact CategoryTheory.congr_fun (i.inv_hom_id_app (op V)) _
  let test (U : Dᵒᵖ) : N.obj.obj U →+
      (∀ (V : C) (g : F.obj V ⟶ U.unop),
        (ModuleCat.restrictScalars (R.obj.map g.op).hom).obj (M.val.obj (op V))) :=
    { toFun := fun n V g ↦ (i.hom.app (op V)).hom (N.obj.map g.op n)
      map_zero' := by
        funext V g
        exact map_zero ((i.hom.app (op V)).hom.comp (N.obj.map g.op).hom)
      map_add' := by
        intro n m
        funext V g
        exact map_add ((i.hom.app (op V)).hom.comp (N.obj.map g.op).hom) n m }
  have hinj (U : Dᵒᵖ) : Function.Injective (test U) := by
    intro n m h
    apply Functor.IsCoverDense.ext F Q U.unop
    intro V g
    apply (ConcreteCategory.bijective_of_isIso (i.hom.app (op V))).1
    exact congrFun (congrFun h V) g
  let instSmul (U : Dᵒᵖ) : SMul (R.obj.obj U) (N.obj.obj U) :=
    ⟨fun r n ↦ b.app U (r, n)⟩
  let instMod (U : Dᵒᵖ) : Module (R.obj.obj U) (N.obj.obj U) :=
    Function.Injective.module _ (test U) (hinj U) (by
      intro r n
      funext V g
      exact hres U V g r n)
  let T : SheafOfModules.{u} R :=
    { val := PresheafOfModules.ofPresheaf N.obj (fun {U V} g r n ↦ by
        exact (congrArg (fun h : P.obj U ⟶ Q.obj.obj V ↦ h (r, n))
          (b.naturality g)).symm)
      isSheaf := N.property }
  refine ⟨T, ⟨?_⟩⟩
  apply (fullyFaithfulForget S).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · refine
      { hom := ModuleCat.ofHom
          { toFun := (i.hom.app U).hom
            map_add' := map_add (i.hom.app U).hom
            map_smul' := ?_ }
        inv := ModuleCat.ofHom
          { toFun := (i.inv.app U).hom
            map_add' := map_add (i.inv.app U).hom
            map_smul' := ?_ }
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · intro r n
      exact hact U r n
    · intro r n
      apply (ConcreteCategory.bijective_of_isIso (i.hom.app U)).1
      calc
        (i.hom.app U).hom ((i.inv.app U).hom (r • n)) = r • n :=
          CategoryTheory.congr_fun (i.inv_hom_id_app U) _
        _ = r • (i.hom.app U).hom ((i.inv.app U).hom n) :=
          congrArg (fun m ↦ r • m) (CategoryTheory.congr_fun (i.inv_hom_id_app U) n).symm
        _ = (i.hom.app U).hom
            (b.app (F.op.obj U) (r, (i.inv.app U).hom n)) := (hact U r _).symm
    · ext n
      exact CategoryTheory.congr_fun (i.hom_inv_id_app U) n
    · ext n
      exact CategoryTheory.congr_fun (i.inv_hom_id_app U) n
  · intro U V g
    ext n
    exact CategoryTheory.congr_fun (i.hom.naturality g) n

/-- Module restriction to a dense subsite is an equivalence whenever restriction of
additive sheaves is an equivalence, without changing the section universe.

Source: Stacks Project, Sites, Tag 03A0; Modules on Sites, Tags 03D1 and 03D2
(blueprint: lem-sfb-dense-subsite-module-extension).

Proof: morphisms of underlying additive sheaves extend uniquely by density, and their
linearity can be checked on the covering sieve of image objects. For essential
surjectivity, extend the additive sheaf and its scalar action as described above;
the counit of additive comparison is linear and yields the required module isomorphism. -/
theorem denseRestriction_isEquivalence
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} (F : C ⥤ D)
    [F.IsDenseSubsite J K]
    [(F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).IsEquivalence]
    (R : Sheaf K RingCat.{u}) :
    (pushforward.{u} (F := F)
      (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R))).IsEquivalence := by
  have := Functor.IsDenseSubsite.isCoverDense J K F
  have := Functor.IsDenseSubsite.isLocallyFull J K F
  let h : (denseRestriction (J := J) F R).FullyFaithful :=
    { preimage := extendHom (J := J) F R
      map_preimage := extendHom_restrict (J := J) F R
      preimage_map := fun _ ↦
        restrictHom_injective (J := J) F R (extendHom_restrict (J := J) F R _) }
  exact ⟨h.faithful, h.full, denseRestriction_essSurj (J := J) F R⟩

end SheafOfModules
