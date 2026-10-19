/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.CategoryTheory.Abelian.ExtRightDerivedHom
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Natural evaluation of a sheaf cohomology class on an injective resolution

Source: Stacks Project, Cohomology on Sites, Section 21.2; Mathlib's computation
of Ext using injective resolutions.
(blueprint: lem-sc-cohomology-resolution-evaluation-natural)
-/

@[expose] public section

universe z w v u

open CategoryTheory

namespace CategoryTheory.Sheaf

set_option maxHeartbeats 450000 in
-- Comparing the two Ext universes and the lifted homology composites needs more reductions.
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation on a terminal object computes cohomology, naturally for resolution maps.
Source: Stacks Project, Cohomology on Sites, Section 21.2; Mathlib
`InjectiveResolution.extMk_comp_mk₀`.
(blueprint: lem-sc-cohomology-resolution-evaluation-natural)

Proof: Let Z be the constant sheaf of lifted integers. The constant-sheaf
adjunction and evaluation at 1 identify Hom(Z,G) additively with G(T), naturally
in G. Lift G(T) to the universe of the Hom groups and package this as a natural
isomorphism b. Compute Ext in that Hom universe using hasExt_of_enoughInjectives.
Ext.homAddEquiv and its inverse reindex the given Ext groups into this universe.
The reindexing commutes with postcomposition: both sides have the same derived
morphism by Ext.comp_hom and Ext.mk₀_hom. Apply the library's proved natural
Ext/derived-Hom comparison, then compute derived Hom on R by isoRightDerivedObj.
Apply homology to b.mapHomologicalComplex on R, and use mapHomologyIso for ULift
followed by lowering. These comparisons give e before theta and phi are introduced.
For phi over theta, combine naturality of the Ext/derived-Hom comparison,
isoRightDerivedObj_hom_naturality, naturality of b on complexes after applying
homology, and mapHomologyIso_hom_naturality. Lowering this equality gives the
claimed equation. This also works for the zero sheaf and arbitrary terminal
objects; no nonemptiness assumption on the site is used.
-/
theorem exists_cohomology_resolution_evaluation_natural_succ
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{z} (Sheaf J AddCommGrpCat.{w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    (T : C) (hT : Limits.IsTerminal T) (F : Sheaf J AddCommGrpCat.{w})
    (R : InjectiveResolution F) (q : ℕ) :
    let E := sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op T)
    ∃ e : Sheaf.H F (q + 1) ≃+
        ((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (q + 1),
      ∀ (θ : F ⟶ F) (φ : R.cocomplex ⟶ R.cocomplex)
        (_ : R.ι.f 0 ≫ φ.f 0 = θ ≫ R.ι.f 0) (x : Sheaf.H F (q + 1)),
        e (Sheaf.H.map.{z, w, v, u} θ (q + 1) x) =
          HomologicalComplex.homologyMap
            ((E.mapHomologicalComplex (.up ℕ)).map φ) (q + 1) (e x)  := by
  classical
  let E := sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op T)
  let Z := (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))
  let A := AddCommGrpCat.uliftFunctor.{u, w}
  let B := preadditiveCoyoneda.obj (Opposite.op Z)
  let d (G : Sheaf J AddCommGrpCat.{w}) : (Z ⟶ G) ≃+ A.obj (E.obj G) :=
    ((constantSheafAdj J AddCommGrpCat hT).homAddEquiv _ G).trans
      ((AddCommGrpCat.uliftZMultiplesAddEquiv _).trans AddEquiv.ulift.symm)
  have hd {G G' : Sheaf J AddCommGrpCat.{w}} (f : G ⟶ G') (a : Z ⟶ G) :
      d G' (a ≫ f) = A.map (E.map f) (d G a) := by
    change ULift.up
        (((constantSheafAdj J AddCommGrpCat hT).homEquiv _ G') (a ≫ f) (ULift.up 1)) =
      ULift.up (f.hom.app (Opposite.op T)
        (((constantSheafAdj J AddCommGrpCat hT).homEquiv _ G) a (ULift.up 1)))
    rw [Adjunction.homEquiv_naturality_right]
    rfl
  let b : B ≅ E ⋙ A := NatIso.ofComponents (fun G ↦ (d G).toAddCommGrpIso) (by
    intro G G' f
    ext a
    exact hd f a)
  let : HasDerivedCategory (Sheaf J AddCommGrpCat.{w}) := HasDerivedCategory.standard _
  let : HasExt.{max u w} (Sheaf J AddCommGrpCat.{w}) :=
    hasExt_of_enoughInjectives _
  let r : @Sheaf.H _ _ J F _ ‹HasExt.{z} (Sheaf J AddCommGrpCat.{w})› (q + 1) ≃+
      Abelian.Ext.{max u w} Z F (q + 1) :=
    Abelian.Ext.homAddEquiv.{_, z}.trans Abelian.Ext.homAddEquiv.{_, max u w}.symm
  obtain ⟨c⟩ := nonempty_extFunctor_iso_rightDerivedHom Z (q + 1)
  let k := (NatIso.mapHomologicalComplex b (.up ℕ)).app R.cocomplex
  let l := (HomologicalComplex.homologyFunctor _ _ (q + 1)).mapIso k
  let K := (E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  let t := (K.sc (q + 1)).mapHomologyIso A
  let m := (R.isoRightDerivedObj B (q + 1)) ≪≫ l
  let e := r.trans ((c.app F ≪≫ m ≪≫ t).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)
  refine ⟨e, ?_⟩
  intro θ φ comm x
  have hr : r (Sheaf.H.map.{z, w, v, u} θ (q + 1) x) =
      ((Abelian.extFunctor (q + 1)).obj (Opposite.op Z)).map θ (r x) := by
    have hx : (r x).hom = x.hom := by
      change Abelian.Ext.homAddEquiv.{_, max u w}
        (Abelian.Ext.homAddEquiv.{_, max u w}.symm _) = _
      exact AddEquiv.apply_symm_apply _ _
    apply Abelian.Ext.homAddEquiv.{_, max u w}.injective
    change Abelian.Ext.homAddEquiv.{_, max u w}
      (Abelian.Ext.homAddEquiv.{_, max u w}.symm _) = _
    rw [AddEquiv.apply_symm_apply]
    change (x.comp (Abelian.Ext.mk₀ θ) (add_zero _)).hom =
      ((r x).comp (Abelian.Ext.mk₀ θ) (add_zero _)).hom
    simp only [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, hx]
  have hc := ConcreteCategory.congr_hom (c.hom.naturality θ) (r x)
  have hm := R.isoRightDerivedObj_hom_naturality θ R φ comm B (q + 1)
  have hk := (NatIso.mapHomologicalComplex b (.up ℕ)).hom.naturality φ
  have hl := (HomologicalComplex.homologyFunctor _ _ (q + 1)).congr_map hk
  simp only [HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyMap_comp] at hl
  have ht := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) (q + 1)).map
      ((E.mapHomologicalComplex (.up ℕ)).map φ)) A
  change (t.hom (l.hom ((R.isoRightDerivedObj B (q + 1)).hom
    ((c.app F).hom (r (Sheaf.H.map.{z, w, v, u} θ (q + 1) x)))))).down = _
  rw [hr]
  rw [show (c.app F).hom
      (((Abelian.extFunctor (q + 1)).obj (Opposite.op Z)).map θ (r x)) =
      (B.rightDerived (q + 1)).map θ ((c.app F).hom (r x)) from hc]
  rw [show (R.isoRightDerivedObj B (q + 1)).hom
      ((B.rightDerived (q + 1)).map θ ((c.app F).hom (r x))) =
      HomologicalComplex.homologyMap ((B.mapHomologicalComplex (.up ℕ)).map φ)
        (q + 1) ((R.isoRightDerivedObj B (q + 1)).hom ((c.app F).hom (r x))) from
          ConcreteCategory.congr_hom hm ((c.app F).hom (r x))]
  have hl' := ConcreteCategory.congr_hom hl
    ((R.isoRightDerivedObj B (q + 1)).hom ((c.app F).hom (r x)))
  change l.hom (HomologicalComplex.homologyMap
    ((B.mapHomologicalComplex (.up ℕ)).map φ) (q + 1) _) =
    HomologicalComplex.homologyMap (((E ⋙ A).mapHomologicalComplex (.up ℕ)).map φ)
      (q + 1) (l.hom _) at hl'
  rw [hl']
  have he : e x = (t.hom (l.hom
      ((R.isoRightDerivedObj B (q + 1)).hom ((c.app F).hom (r x))))).down := by
    rfl
  have hf := congrArg
    (fun a ↦ HomologicalComplex.homologyMap
      ((E.mapHomologicalComplex (.up ℕ)).map φ) (q + 1) a) he
  exact (congrArg ULift.down (ConcreteCategory.congr_hom ht
    (l.hom ((R.isoRightDerivedObj B (q + 1)).hom ((c.app F).hom (r x)))))).trans hf.symm


end CategoryTheory.Sheaf
