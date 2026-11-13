/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.CompletionInternalHomAffineSectionsLift
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.Topology.Sheaves.Sheaf

/-! # Unique section lifts of compatible quotient morphisms

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem affine_obj_ext {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (s t : M.val.obj (op U))
    (h : ∀ (V : X.affineOpens) (f : V.val ⟶ U),
      M.val.map f.op s = M.val.map f.op t) : s = t := by
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact ⟨V, hVU, hxV, h ⟨V, hV⟩ (homOfLE hVU)⟩

private theorem affine_coversTop (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).CoversTop
      (fun U : X.affineOpens ↦ U.val) := by
  intro U x hx
  obtain ⟨V, hV, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact ⟨V, homOfLE hVU, ⟨⟨V, hV⟩, ⟨𝟙 V⟩⟩, hxV⟩

private theorem compatible_sections_lift_of_affine {X : Scheme.{u}}
    (S : ℕᵒᵖ ⥤ X.Modules) (T : ℕᵒᵖ → X.Modules)
    (e : ∀ n, S.obj n ⟶ T n) (r : ∀ n, (T n).sections)
    (hlocal : ∀ U : X.affineOpens,
      ∃! s : {s : ∀ n, (S.obj n).val.obj (op U.val) //
        ∀ (a b : ℕᵒᵖ) (f : a ⟶ b), (S.map f).val.app (op U.val) (s a) = s b},
        ∀ n, (e n).val.app (op U.val) (s.val n) = (r n).val (op U.val)) :
    ∃! s : {s : ∀ n, (S.obj n).sections //
      ∀ (a b : ℕᵒᵖ) (f : a ⟶ b), SheafOfModules.sectionsMap (S.map f) (s a) = s b},
      ∀ n, SheafOfModules.sectionsMap (e n) (s.val n) = r n := by
  classical
  choose l hl hu using hlocal
  have hrestrict (U V : X.affineOpens) (f : V.val ⟶ U.val) :
      (⟨fun n ↦ (S.obj n).val.map f.op ((l U).val n), by
        intro a b g
        exact (PresheafOfModules.naturality_apply (S.map g).val f.op ((l U).val a)).trans
          (congrArg ((S.obj b).val.map f.op) ((l U).property a b g))⟩ :
        {s : ∀ n, (S.obj n).val.obj (op V.val) //
          ∀ (a b : ℕᵒᵖ) (g : a ⟶ b), (S.map g).val.app (op V.val) (s a) = s b}) =
        l V := by
    apply hu V
    intro n
    exact (PresheafOfModules.naturality_apply (e n).val f.op ((l U).val n)).trans
      ((congrArg ((T n).val.map f.op) (hl U n)).trans ((r n).property f.op))
  have hcompatible (n : ℕᵒᵖ) :
      Presheaf.FamilyOfElementsOnObjects.IsCompatible
        (F := (S.obj n).val.presheaf ⋙ forget _)
        (Y := fun U : X.affineOpens ↦ U.val) (fun U ↦ (l U).val n) := by
    intro W U V f g
    apply affine_obj_ext (S.obj n) W
    intro Z k
    change (S.obj n).val.map k.op ((S.obj n).val.map f.op _) =
      (S.obj n).val.map k.op ((S.obj n).val.map g.op _)
    have hU := congrArg (fun s ↦ s.val n) (hrestrict U Z (k ≫ f))
    have hV := congrArg (fun s ↦ s.val n) (hrestrict V Z (k ≫ g))
    simpa only [op_comp, PresheafOfModules.map_comp_apply] using hU.trans hV.symm
  have hsheaf (M : X.Modules) :
      Presheaf.IsSheaf (Opens.grothendieckTopology X)
        (M.val.presheaf ⋙ forget _) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _) M.isSheaf
  obtain ⟨s, hs⟩ : ∃ s : ∀ n, (S.obj n).sections,
      ∀ n U, (s n).val (op U.val) = (l U).val n := by
    choose s hs using fun n ↦
      (hcompatible n).existsUnique_section (affine_coversTop X) (hsheaf (S.obj n))
    exact ⟨s, fun n ↦ (hs n).1⟩
  have hext (M : X.Modules) (s t : M.sections)
      (h : ∀ U : X.affineOpens, s.val (op U.val) = t.val (op U.val)) : s = t :=
    (affine_coversTop X).sections_ext ⟨_, hsheaf M⟩ h
  have htrans (a b : ℕᵒᵖ) (f : a ⟶ b) :
      SheafOfModules.sectionsMap (S.map f) (s a) = s b := by
    apply hext
    intro U
    change (S.map f).val.app _ ((s a).val _) = (s b).val _
    rw [hs a U, hs b U]
    exact (l U).property a b f
  refine ⟨⟨s, htrans⟩, ?_, ?_⟩
  · intro n
    apply hext
    intro U
    change (e n).val.app _ ((s n).val _) = (r n).val _
    rw [hs n U]
    exact hl U n
  · intro s' hs'
    apply Subtype.ext
    funext n
    apply hext
    intro U
    let l' : {s : ∀ n, (S.obj n).val.obj (op U.val) //
        ∀ (a b : ℕᵒᵖ) (f : a ⟶ b), (S.map f).val.app (op U.val) (s a) = s b} :=
      ⟨fun n ↦ (s'.val n).val (op U.val), fun a b f ↦
        congrArg (fun s ↦ s.val (op U.val)) (s'.property a b f)⟩
    have hl' : l' = l U := hu U l' (fun n ↦
      congrArg (fun s ↦ s.val (op U.val)) (hs' n))
    exact (congrArg (fun l ↦ l.val n) hl').trans (hs n U).symm

/-- Every compatible family of maps between the completed quotient terms has a
unique lift to compatible sections of the quotients of internal Hom. The maps e
are required to be the quotient factorizations of postcomposition.

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, affine-local proof;
Lemma 087W, and Algebra, Lemmas 00MA and 00MB; More on Algebra, Lemma 087R. -/
theorem completion_internal_hom_sections_lift {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F G : CoherentModules X)
    (e : ∀ n : ℕᵒᵖ,
      formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) G.obj F.obj) ⟶
        SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) (formalModuleQuotient I (n.unop + 1) G.obj)
          (formalModuleQuotient I (n.unop + 1) F.obj))
    (he : ∀ n : ℕᵒᵖ,
        formalModuleQuotientπ I (n.unop + 1) (SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
          e n ≫ SheafOfModules.homObjMap
            (R := X.toRingedSpace.sheaf) (formalModuleQuotientπ I (n.unop + 1) G.obj)
            (𝟙 (formalModuleQuotient I (n.unop + 1) F.obj)) =
        SheafOfModules.homObjMap
          (R := X.toRingedSpace.sheaf) (𝟙 G.obj) (formalModuleQuotientπ I (n.unop + 1) F.obj))
    (t : ∀ n : ℕᵒᵖ, formalModuleQuotient I (n.unop + 1) G.obj ⟶
      formalModuleQuotient I (n.unop + 1) F.obj)
    (ht : ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
      t a ≫ (formalCompletionSystem I F.obj).map f =
        (formalCompletionSystem I G.obj).map f ≫ t b) :
    ∃! s : {s : ∀ n : ℕᵒᵖ,
          (formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
            (R := X.toRingedSpace.sheaf) G.obj F.obj)).sections //
          ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
            SheafOfModules.sectionsMap
              ((formalCompletionSystem I (SheafOfModules.homObj
                (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f)
              (s a) = s b}, ∀ n : ℕᵒᵖ,
      SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
        (formalModuleQuotient I (n.unop + 1) G.obj)
        (formalModuleQuotient I (n.unop + 1) F.obj)
        (SheafOfModules.sectionsMap (e n) (s.val n)) = t n := by
  let T (n : ℕᵒᵖ) := SheafOfModules.homObj (R := X.toRingedSpace.sheaf)
    (formalModuleQuotient I (n.unop + 1) G.obj)
    (formalModuleQuotient I (n.unop + 1) F.obj)
  let E (n : ℕᵒᵖ) := SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
    (formalModuleQuotient I (n.unop + 1) G.obj)
    (formalModuleQuotient I (n.unop + 1) F.obj)
  obtain ⟨s, hs, hu⟩ := compatible_sections_lift_of_affine
    (formalCompletionSystem I (SheafOfModules.homObj
      (R := X.toRingedSpace.sheaf) G.obj F.obj)) T e (fun n ↦ (E n).symm (t n))
    (completion_internal_hom_affine_sections_lift I F G e he t ht)
  refine ⟨s, fun n ↦ ?_, fun s' hs' ↦ hu s' (fun n ↦ ?_)⟩
  · exact (congrArg (E n) (hs n)).trans ((E n).apply_symm_apply (t n))
  · exact (E n).injective ((hs' n).trans ((E n).apply_symm_apply (t n)).symm)

end AlgebraicGeometry
