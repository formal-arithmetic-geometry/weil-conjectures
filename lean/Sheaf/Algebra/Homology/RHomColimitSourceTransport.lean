/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses

/-! # Source transport of the internal-Hom colimit comparison

Source: Stacks Project, Cohomology on Sites, Tags 0A8X, 0A95, 08J7 and 08JC;
the source-localization and signed-cocone calculation in the node
(blueprint: lem-sfb-rhom-colimit-source-transport).

The source of the comparison is the localization of the termwise colimit of the
fixed complex models. It is not defined as a colimit in the derived category.
The factorization and its natural comparison express independence of representatives.
The last clause specifies the shift transport as the image of a chain-level colimit map.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false


noncomputable section

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedHomUniverses

namespace CategoryTheory.RingedHomColimitTransport

section Abstract

variable {X A B K : Type*} [Category X] [Category A] [Category B] [Category K]
  [HasColimitsOfShape K A]

private def colimitComparison (U : X ⥤ A ⥤ A) (Q : A ⥤ B) :
    U ⋙ Functor.whiskeringRight K A A ⋙
        (Functor.whiskeringRight (K ⥤ A) (K ⥤ A) B).obj (colim ⋙ Q) ⟶
      U ⋙ (Functor.whiskeringRight A A B).obj Q ⋙
        (Functor.whiskeringLeft (K ⥤ A) A B).obj colim where
  app x := {
    app := fun N ↦ Q.map (colimit.post N (U.obj x))
    naturality := fun N N' f ↦ by
      dsimp
      simp only [← Q.map_comp]
      exact congrArg Q.map (colimit.map_post f (U.obj x)).symm }
  naturality := by
    intro x y f
    ext N
    change Q.map (colim.map (Functor.whiskerLeft N (U.map f))) ≫
        Q.map (colimit.post N (U.obj y)) =
      Q.map (colimit.post N (U.obj x)) ≫ Q.map ((U.map f).app (colimit N))
    simp only [← Q.map_comp]
    congr 1
    apply colimit.hom_ext
    intro i
    simp only [colimit.ι_map_assoc, Functor.whiskerLeft_app, colimit.ι_post,
      colimit.ι_post_assoc]
    exact ((U.map f).naturality (colimit.ι N i)).symm

private theorem colimit_shift_square (F G S : A ⥤ A)
    [PreservesColimitsOfShape K S] (σ : F ≅ G ⋙ S) (N : K ⥤ A) :
    colimit.post N F ≫ σ.hom.app (colimit N) =
      colim.map (Functor.whiskerLeft N σ.hom) ≫
        (preservesColimitIso S (N ⋙ G)).inv ≫ S.map (colimit.post N G) := by
  apply colimit.hom_ext
  intro i
  rw [colimit.ι_post_assoc, colimit.ι_map_assoc]
  change F.map (colimit.ι N i) ≫ σ.hom.app (colimit N) =
    σ.hom.app (N.obj i) ≫ colimit.ι ((N ⋙ G) ⋙ S) i ≫
      (preservesColimitIso S (N ⋙ G)).inv ≫ S.map (colimit.post N G)
  rw [ι_preservesColimitIso_inv_assoc, ← S.map_comp, colimit.ι_post]
  exact σ.hom.naturality (colimit.ι N i)

private def colimitShiftIso [HasShift A ℤ] [HasShift B ℤ]
    (U : X ⥤ A ⥤ A) (Q : A ⥤ B) [Q.CommShift ℤ]
    (n : ℤ) :
    U ⋙ (Functor.whiskeringRight A A A).obj (shiftFunctor A n) ⋙
        Functor.whiskeringRight K A A ⋙
          (Functor.whiskeringRight (K ⥤ A) (K ⥤ A) B).obj (colim ⋙ Q) ≅
      U ⋙ Functor.whiskeringRight K A A ⋙
        (Functor.whiskeringRight (K ⥤ A) (K ⥤ A) B).obj (colim ⋙ Q) ⋙
          (Functor.whiskeringRight (K ⥤ A) B B).obj (shiftFunctor B n) := by
  let e : (Functor.whiskeringRight K A A).obj (shiftFunctor A n) ⋙ colim ⋙ Q ≅
      colim ⋙ Q ⋙ shiftFunctor B n :=
    Functor.isoWhiskerRight (preservesColimitNatIso (shiftFunctor A n)).symm Q ≪≫
      Functor.isoWhiskerLeft colim (Q.commShiftIso n)
  exact Functor.isoWhiskerLeft (U ⋙ Functor.whiskeringRight K A A)
    ((Functor.whiskeringRight (K ⥤ A) (K ⥤ A) B).mapIso e)

set_option backward.isDefEq.respectTransparency false in
private theorem sourceShiftDescent
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ]
    (W : MorphismProperty A) [W.ContainsIdentities] [Q.IsLocalization W]
    (U : Aᵒᵖ × A ⥤ A) (I : A ⥤ A) (η : 𝟭 A ⟶ I)
    (H : Bᵒᵖ × B ⥤ B)
    (fac : (Q.op.prod Q) ⋙ H ≅ (𝟭 _).prod I ⋙ U ⋙ Q)
    (s : ℤ)
    (e : U ⋙ shiftFunctor A (-s) ≅
      ((shiftFunctor A s).op.prod (𝟭 A)) ⋙ U) :
    let α : U ⋙ Q ⟶ (Q.op.prod Q) ⋙ H :=
      Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 Aᵒᵖ)) η) (U ⋙ Q) ≫ fac.inv
    ∃ t : H ⋙ shiftFunctor B (-s) ≅
      ((shiftFunctor B s).op.prod (𝟭 B)) ⋙ H,
      (∀ (L M : A),
        (Q.commShiftIso (-s)).hom.app (U.obj (op L, M)) ≫
            (α.app (op L, M))⟦-s⟧' ≫ t.hom.app (op (Q.obj L), Q.obj M) =
          Q.map ((e.app (op L, M)).hom) ≫ α.app (op (L⟦s⟧), M) ≫
            H.map (Prod.mkHom (((Q.commShiftIso s).inv.app L).op) (𝟙 _))) ∧
      ∀ (L M : A), t.hom.app (op (Q.obj L), Q.obj M) =
        (fac.hom.app (op L, M))⟦-s⟧' ≫
          (Q.commShiftIso (-s)).inv.app (U.obj (op L, I.obj M)) ≫
          Q.map ((e.app (op L, I.obj M)).hom) ≫
          fac.inv.app (op (L⟦s⟧), M) ≫
          H.map (Prod.mkHom (((Q.commShiftIso s).inv.app L).op) (𝟙 _)) := by
  classical
  intro α
  let P := Q.op.prod Q
  let V := W.op.prod W
  let S := (shiftFunctor A s).op.prod (𝟭 A)
  let q : S ⋙ P ≅ P ⋙ ((shiftFunctor B s).op.prod (𝟭 B)) :=
    NatIso.prod (NatIso.op (Q.commShiftIso s).symm) (Iso.refl Q)
  let f : P ⋙ (H ⋙ shiftFunctor B (-s)) ≅
      P ⋙ (((shiftFunctor B s).op.prod (𝟭 B)) ⋙ H) :=
    Functor.isoWhiskerRight fac (shiftFunctor B (-s)) ≪≫
      Functor.isoWhiskerLeft ((𝟭 _).prod I ⋙ U) (Q.commShiftIso (-s)).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft ((𝟭 _).prod I) e) Q ≪≫
      (Functor.isoWhiskerLeft S fac).symm ≪≫ Functor.isoWhiskerRight q H
  let ff := Localization.fullyFaithfulWhiskeringLeft P V B
  let t := ff.preimageIso f
  refine ⟨t, ?_, ?_⟩
  · intro L M
    have ht : t.hom.app (P.obj (op L, M)) = f.hom.app (op L, M) :=
      NatTrans.congr_app (ff.map_preimage f.hom) (op L, M)
    dsimp only [P, Functor.prod_obj, Functor.op_obj] at ht
    rw [ht]
    dsimp only [f, α, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
      Category.id_comp]
    dsimp only [Functor.comp_map, Functor.comp_obj, NatTrans.prod, NatTrans.id_app,
      Functor.id_obj, Functor.prod_obj, Functor.whiskerLeft_app]
    rw [← Functor.commShiftIso_hom_naturality_assoc,
      Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc]
    have hn := e.hom.naturality (Prod.mkHom (𝟙 (op L)) (η.app M))
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
      Functor.prod_map, Functor.op_map, Functor.id_map, Functor.map_id,
      Functor.op_obj, Functor.id_obj] at hn
    rw [hn]
    simp only [unop_id, Functor.map_id, op_id, Functor.map_comp, Category.assoc]
    rfl
  · intro L M
    have ht := NatTrans.congr_app (ff.map_preimage f.hom) (op L, M)
    change t.hom.app (op (Q.obj L), Q.obj M) = _ at ht
    rw [ht]
    dsimp only [f, q, S, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj, NatIso.prod,
      NatIso.op, NatTrans.prod, NatTrans.op, Iso.refl_hom, NatTrans.id_app]
    rfl


private theorem descendShiftIso
    {E : Type*} [Category E] [HasShift A ℤ] [HasShift B ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ]
    (W : MorphismProperty A) [Q.IsLocalization W]
    (F : Aᵒᵖ ⥤ E) (G : Bᵒᵖ ⥤ E) (rho : Q.op ⋙ G ≅ F)
    (T : E ⥤ E) (n : ℤ)
    (b : (shiftFunctor A n).op ⋙ F ≅ F ⋙ T) :
    ∃ t : (shiftFunctor B n).op ⋙ G ≅ G ⋙ T,
      ∀ L : A,
        rho.inv.app (op (L⟦n⟧)) ≫
            G.map ((Q.commShiftIso n).inv.app L).op ≫ t.hom.app (op (Q.obj L)) =
          b.hom.app (op L) ≫ T.map (rho.inv.app (op L)) := by
  let q : (shiftFunctor A n).op ⋙ Q.op ≅ Q.op ⋙ (shiftFunctor B n).op :=
    NatIso.op (Q.commShiftIso n).symm
  let f : Q.op ⋙ ((shiftFunctor B n).op ⋙ G) ≅ Q.op ⋙ (G ⋙ T) :=
    (Functor.isoWhiskerRight q G).symm ≪≫
      Functor.isoWhiskerLeft (shiftFunctor A n).op rho ≪≫ b ≪≫
        Functor.isoWhiskerRight rho.symm T
  let ff := Localization.fullyFaithfulWhiskeringLeft Q.op W.op E
  let t := ff.preimageIso f
  refine ⟨t, ?_⟩
  intro L
  have ht := NatTrans.congr_app (ff.map_preimage f.hom) (op L)
  change t.hom.app (op (Q.obj L)) = _ at ht
  rw [ht]
  dsimp only [f, q, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.op_obj, NatIso.op, NatTrans.op]
  simp only [← G.map_comp_assoc, ← op_comp, Iso.hom_inv_id_app, op_id]
  erw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem signedShiftNaturality
    {A₀ B₀ : Type*} [Category A₀] [Preadditive A₀]
    [Category B₀] [Preadditive B₀]
    (F : (CochainComplex A₀ ℤ)ᵒᵖ ⥤ CochainComplex A₀ ℤ ⥤ CochainComplex B₀ ℤ)
    (V : A₀ → A₀ → B₀)
    (Vmap : ∀ {a a' b b'}, (a' ⟶ a) → (b ⟶ b') → (V a b ⟶ V a' b'))
    (π : ∀ (L M : CochainComplex A₀ ℤ) (k p q : ℤ), p + k = q →
      (((F.obj (op L)).obj M).X k ⟶ V (L.X p) (M.X q)))
    (hExt : ∀ (L M : CochainComplex A₀ ℤ) (k : ℤ) (Z : B₀)
      (a b : Z ⟶ ((F.obj (op L)).obj M).X k),
      (∀ p q h, a ≫ π L M k p q h = b ≫ π L M k p q h) → a = b)
    (hMap : ∀ {L L' M M' : CochainComplex A₀ ℤ} (f : L' ⟶ L) (g : M ⟶ M')
      (k p q : ℤ) (h : p + k = q),
      (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f k ≫ π L' M' k p q h =
        π L M k p q h ≫ Vmap (f.f p) (g.f q))
    (n : ℤ)
    (e : ∀ L M : CochainComplex A₀ ℤ,
      (((F.obj (op L)).obj M)⟦-n⟧) ≅ ((F.obj (op (L⟦n⟧))).obj M))
    (he : ∀ L M k p q h, (e L M).hom.f k ≫ π (L⟦n⟧) M k p q h =
      (n * k).negOnePow • π L M (k + -n) (p + n) q (by omega)) :
    ∀ (X Y : (CochainComplex A₀ ℤ)ᵒᵖ × CochainComplex A₀ ℤ) (f : X ⟶ Y),
      (Functor.uncurry.obj F ⋙ shiftFunctor _ (-n)).map f ≫ (e Y.1.unop Y.2).hom =
        (e X.1.unop X.2).hom ≫
          (((shiftFunctor (CochainComplex A₀ ℤ) n).op.prod (𝟭 _)) ⋙
            Functor.uncurry.obj F).map f := by
  intro X Y f
  apply HomologicalComplex.hom_ext
  intro k
  apply hExt
  intro p q hpq
  change (((shiftFunctor _ (-n)).map
      ((F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2)).f k ≫
      (e Y.1.unop Y.2).hom.f k) ≫ π (Y.1.unop⟦n⟧) Y.2 k p q hpq =
    ((e X.1.unop X.2).hom.f k ≫
      ((F.map (((shiftFunctor _ n).map f.1.unop).op)).app X.2 ≫
        (F.obj (op (Y.1.unop⟦n⟧))).map f.2).f k) ≫
      π (Y.1.unop⟦n⟧) Y.2 k p q hpq
  rewrite (config := { transparency := .all }) [Category.assoc, he]
  dsimp only [CochainComplex.shiftFunctor_obj_X', CochainComplex.shiftFunctor_map_f']
  rewrite (config := { transparency := .all })
    [Linear.comp_units_smul, hMap f.1.unop f.2, Category.assoc,
    hMap ((shiftFunctor _ n).map f.1.unop) f.2, ← Category.assoc, he,
    Linear.units_smul_comp, CochainComplex.shiftFunctor_map_f']
  rfl

private def curryShift
    {X₀ Y₀ Z₀ T₀ : Type*} [Category X₀] [Category Y₀] [Category Z₀] [Category T₀]
    (H : X₀ × Y₀ ⥤ Z₀) (A : X₀ ⥤ X₀) (S : Z₀ ⥤ Z₀) (I' : T₀ ⥤ Y₀)
    (e : H ⋙ S ≅ (A.prod (𝟭 _)) ⋙ H) :
    A ⋙ Functor.curry.obj H ⋙ (Functor.whiskeringLeft _ _ _).obj I' ≅
      Functor.curry.obj H ⋙ (Functor.whiskeringLeft _ _ _).obj I' ⋙
        (Functor.whiskeringRight _ _ _).obj S :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ e.symm.app (X, I'.obj Y)) (by
      intro Y Y' f
      change H.map (Prod.mkHom (𝟙 (A.obj X)) (I'.map f)) ≫
          e.inv.app (X, I'.obj Y') =
        e.inv.app (X, I'.obj Y) ≫ S.map (H.map (Prod.mkHom (𝟙 X) (I'.map f)))
      simpa only [Functor.comp_map, Functor.prod_map, Functor.map_id, Functor.id_map]
        using e.inv.naturality (Prod.mkHom (𝟙 X) (I'.map f)))) (by
    intro X X' f
    apply NatTrans.ext
    funext Y
    change H.map (Prod.mkHom (A.map f) (𝟙 (I'.obj Y))) ≫
        e.inv.app (X', I'.obj Y) =
      e.inv.app (X, I'.obj Y) ≫ S.map (H.map (Prod.mkHom f (𝟙 (I'.obj Y))))
    simpa only [Functor.comp_map, Functor.prod_map, Functor.map_id, Functor.id_map]
      using e.inv.naturality (Prod.mkHom f (𝟙 (I'.obj Y))))

private def curryShiftOfCurried
    {X₀ Y₀ Z₀ T₀ : Type*} [Category X₀] [Category Y₀] [Category Z₀] [Category T₀]
    (F : X₀ ⥤ Y₀ ⥤ Z₀) (A : X₀ ⥤ X₀) (S : Z₀ ⥤ Z₀) (I' : T₀ ⥤ Y₀)
    (e : Functor.uncurry.obj F ⋙ S ≅ (A.prod (𝟭 _)) ⋙ Functor.uncurry.obj F) :
    A ⋙ F ⋙ (Functor.whiskeringLeft _ _ _).obj I' ≅
      F ⋙ (Functor.whiskeringLeft _ _ _).obj I' ⋙
        (Functor.whiskeringRight _ _ _).obj S :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ e.symm.app (X, I'.obj Y)) (by
      intro Y Y' f
      simpa only [Functor.comp_map, Functor.prod_map, Functor.map_id, Functor.id_map,
        Functor.uncurry_obj_obj, Functor.uncurry_obj_map, NatTrans.id_app, Category.id_comp,
        Iso.app_hom, Iso.symm_hom, NatIso.ofComponents_hom_app,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
        Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map,
        Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map,
        Functor.whiskerRight_app] using
        e.inv.naturality (Prod.mkHom (𝟙 X) (I'.map f)))) (by
    intro X X' f
    apply NatTrans.ext
    funext Y
    simpa only [Functor.comp_map, Functor.prod_map, Functor.map_id, Functor.id_map,
      Functor.uncurry_obj_obj, Functor.uncurry_obj_map, NatTrans.id_app,
      Category.comp_id, NatTrans.comp_app,
      Iso.app_hom, Iso.symm_hom, NatIso.ofComponents_hom_app,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
      Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map,
      Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map,
      Functor.whiskerLeft_app, Functor.whiskerRight_app] using
      e.inv.naturality (Prod.mkHom f (𝟙 (I'.obj Y))))

private theorem shiftComparisonSquare
    {A₀ B₀ : Type*} [Category A₀] [Category B₀]
    [HasShift A₀ ℤ] [HasShift B₀ ℤ]
    (Q : A₀ ⥤ B₀) [Q.CommShift ℤ] (n : ℤ)
    {x x' y y' : A₀} (a : x ⟶ y) (a' : x' ⟶ y')
    (b : x' ⟶ x⟦n⟧) (e : y⟦n⟧ ⟶ y')
    {d d' d'' : B₀} (fac : d ≅ Q.obj y) (fac' : d' ≅ Q.obj y')
    (q : d' ⟶ d'') (z : d⟦n⟧ ≅ d'')
    (hz : z.hom = fac.hom⟦n⟧' ≫ (Q.commShiftIso n).inv.app y ≫
      Q.map e ≫ fac'.inv ≫ q)
    (hs : b ≫ a⟦n⟧' ≫ e = a') :
    Q.map a' ≫ fac'.inv ≫ q ≫ z.inv =
      (Q.map b ≫ (Q.commShiftIso n).hom.app x) ≫ (Q.map a ≫ fac.inv)⟦n⟧' := by
  apply (cancel_mono z.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hz]
  simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  rw [← Functor.commShiftIso_hom_naturality_assoc, Iso.hom_inv_id_app_assoc]
  simp only [← Q.map_comp_assoc]
  rw [hs]

end Abstract

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]
  {I : Type (max c v r)} [SmallCategory I]
  [HasColimitsOfShape I (Modules.{c, v, r} J R)]

/-- The termwise colimit of the fixed Hom models, followed by derived localization.
Source: Stacks 0A8X, 0A95 and the node's proof, steps 1--3
(blueprint: lem-sfb-rhom-colimit-source-transport).
This is functorial in the source complex and the entire target diagram. -/
noncomputable def strictColimit :
    (Complex.{c, v, r} J R)ᵒᵖ ⥤ (I ⥤ Complex.{c, v, r} J R) ⥤ D.{c, v, r, w} J R :=
  homComplexFunctor.{c, v, max c v r, max c v r} (R := R) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (WeilConjectures.coefficientHomResolution.{r, c, v} J R) ⋙
    Functor.whiskeringRight I _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj (colim ⋙ DerivedCategory.Q)

/-- The target of the comparison, with a derived source and a complex target diagram.
Source: Stacks 08J7 and the node's definition of H(A,N_infinity)
(blueprint: lem-sfb-rhom-colimit-source-transport). -/
noncomputable def target :
    (D.{c, v, r, w} J R)ᵒᵖ ⥤ (I ⥤ Complex.{c, v, r} J R) ⥤ D.{c, v, r, w} J R :=
  Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R) ⋙
    (Functor.whiskeringLeft _ _ _).obj (colim ⋙ DerivedCategory.Q)

private noncomputable abbrev models :
    (Complex.{c, v, r} J R)ᵒᵖ ⥤ Complex.{c, v, r} J R ⥤ Complex.{c, v, r} J R :=
  homComplexFunctor.{c, v, max c v r, max c v r} (R := R) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (WeilConjectures.coefficientHomResolution.{r, c, v} J R)

private def bifunctorComparison :
    (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
        derivedInternalHomOfUniverses.{c, v, r, w} J R ≅
      (𝟭 _).prod (WeilConjectures.coefficientHomResolution.{r, c, v} J R) ⋙
        Functor.uncurry.obj
          (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) ⋙
            DerivedCategory.Q := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  exact Localization.fac _
    (derivedInternalHomOfUniverses_inverts.{c, v, r, w} J R _
      (CochainComplex.toKInjectiveResolution.{max c v r} _)
      (fun F ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r}
        _ F).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r}
          _ F⟩)) (DerivedCategory.Q.op.prod DerivedCategory.Q)

attribute [local irreducible] homComplexFunctor homComplexπ
  derivedInternalHomOfUniverses

private def modelComparison :
    DerivedCategory.Q.op ⋙
        Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R) ⋙
          (Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q ≅
      models.{c, v, r} J R ⋙
        (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q :=
  NatIso.ofComponents (fun L ↦ NatIso.ofComponents
    (fun M ↦ (bifunctorComparison.{c, v, r, w} J R).app (L, M)) (by
      intro M M' f
      change (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map f)) ≫
          (bifunctorComparison.{c, v, r, w} J R).hom.app (L, M') =
        (bifunctorComparison.{c, v, r, w} J R).hom.app (L, M) ≫
          DerivedCategory.Q.map
            (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj L).map
              ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).map f))
      simpa only [Functor.op_obj, Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
        Functor.comp_map, Functor.prod_map, Functor.op_map,
        Functor.id_map, unop_id, op_id, Functor.map_id,
        Functor.uncurry_obj_map, Category.id_comp, NatTrans.id_app] using
        (bifunctorComparison.{c, v, r, w} J R).hom.naturality (Prod.mkHom (𝟙 L) f))) (by
    intro L L' f
    apply NatTrans.ext
    funext M
    change (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (DerivedCategory.Q.map f.unop).op (𝟙 _)) ≫
        (bifunctorComparison.{c, v, r, w} J R).hom.app (L', M) =
      (bifunctorComparison.{c, v, r, w} J R).hom.app (L, M) ≫
        DerivedCategory.Q.map
          (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map f).app
            ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj M))
    simpa only [Functor.op_obj, Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
        Functor.comp_map, Functor.prod_map, Functor.op_map,
      Functor.id_map, Functor.map_id, Functor.uncurry_obj_map, Category.comp_id] using
      (bifunctorComparison.{c, v, r, w} J R).hom.naturality (Prod.mkHom f (𝟙 M)))

private def diagramComparison :
    DerivedCategory.Q.op ⋙ target.{c, v, r, w} (I := I) J R ≅
      models.{c, v, r} J R ⋙ (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q ⋙
        (Functor.whiskeringLeft _ _ _).obj colim :=
  Functor.isoWhiskerRight (modelComparison.{c, v, r, w} J R)
    ((Functor.whiskeringLeft _ _ _).obj colim)

private theorem diagramComparison_app (L : Complex.{c, v, r} J R)
    (N : I ⥤ Complex.{c, v, r} J R) :
    ((diagramComparison.{c, v, r, w} J R).inv.app (op L)).app N =
      (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L (colimit N)).inv := by
  rfl

private def strictComparison :
    strictColimit.{c, v, r, w} (I := I) J R ⟶
      DerivedCategory.Q.op ⋙ target.{c, v, r, w} J R :=
  colimitComparison (models.{c, v, r} J R) DerivedCategory.Q ≫
    (diagramComparison.{c, v, r, w} J R).inv

private theorem strictComparison_app (L : Complex.{c, v, r} J R)
    (N : I ⥤ Complex.{c, v, r} J R) :
    ((strictComparison.{c, v, r, w} J R).app (op L)).app N =
      DerivedCategory.Q.map
        (colimit.post N ((models.{c, v, r} J R).obj (op L))) ≫
          (bifunctorComparison.{c, v, r, w} J R).inv.app (op L, colimit N) := rfl

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)] in
private theorem ordinaryShift_naturality (n : ℤ)
    (e : ∀ L F : Complex.{c, v, r} J R,
      (((homComplexFunctor.{c, v, max c v r, max c v r}
        (R := R)).obj (op L)).obj F)⟦-n⟧ ≅
      ((homComplexFunctor.{c, v, max c v r, max c v r}
        (R := R)).obj (op (L⟦n⟧))).obj F)
    (he : ∀ L F, LeftFormula.{c, v, r} J R L F n (e L F)) :
    ∀ (X Y : (Complex.{c, v, r} J R)ᵒᵖ × Complex.{c, v, r} J R) (f : X ⟶ Y),
      (Functor.uncurry.obj
        (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) ⋙
          shiftFunctor _ (-n)).map f ≫ (e Y.1.unop Y.2).hom =
        (e X.1.unop X.2).hom ≫
          (((shiftFunctor (Complex.{c, v, r} J R) n).op.prod (𝟭 _)) ⋙
            Functor.uncurry.obj
              (homComplexFunctor.{c, v, max c v r, max c v r} (R := R))).map f := by
  let V : Modules.{c, v, r} J R → Modules.{c, v, r} J R →
      Modules.{c, v, r} J R := fun M N ↦ SheafOfModules.homObj (R := R) M N
  let Vmap : ∀ {a a' b b' : Modules.{c, v, r} J R},
      (a' ⟶ a) → (b ⟶ b') → (V a b ⟶ V a' b') :=
    fun f g ↦ SheafOfModules.homObjMap (R := R) f g
  let π (L M : Complex.{c, v, r} J R) (k p q : ℤ) (h : p + k = q) :
      (((homComplexFunctor.{c, v, max c v r, max c v r}
        (R := R)).obj (op L)).obj M).X k ⟶ V (L.X p) (M.X q) :=
    homComplexπ L M k p q h
  refine signedShiftNaturality
    (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) V Vmap π
    ?_ ?_ n e ?_
  · intro L M k Z a b h
    exact homComplex_hom_ext (L := L) (M := M) (n := k) (f := a) (g := b) h
  · intro L L' M M' f g k p q h
    exact homComplexFunctor_map_f_π f g k p q h
  · exact he

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency true in
private theorem ordinaryShift (n : ℤ) :
    ∃ e : Functor.uncurry.obj
          (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) ⋙
          shiftFunctor _ (-n) ≅
        ((shiftFunctor (Complex.{c, v, r} J R) n).op.prod (𝟭 _)) ⋙
          Functor.uncurry.obj
            (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)),
      ∀ (L F : Complex.{c, v, r} J R),
        LeftFormula.{c, v, r} J R L F n (e.app (op L, F)) := by
  classical
  have hS := (leftShift_existsUnique.{c, v, r, w} J R).exists.choose_spec
  have hx (L F : Complex.{c, v, r} J R) :
      ∃ e : (((homComplexFunctor.{c, v, max c v r, max c v r}
          (R := R)).obj (op L)).obj F)⟦-n⟧ ≅
        ((homComplexFunctor.{c, v, max c v r, max c v r}
          (R := R)).obj (op (L⟦n⟧))).obj F,
        LeftFormula.{c, v, r} J R L F n e := by
    obtain ⟨e, he, _⟩ := hS (DerivedCategory.Q.obj L) L F (Iso.refl _) n
    exact ⟨e, he⟩
  choose e he using hx
  exact ⟨NatIso.ofComponents (fun X ↦ e X.1.unop X.2)
    (fun {X Y} f ↦ ordinaryShift_naturality.{c, v, r} J R n e he X Y f), he⟩


set_option backward.isDefEq.respectTransparency true in
private theorem derivedShifts
    (e : ∀ n : ℤ, Functor.uncurry.obj
        (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) ⋙ shiftFunctor _ (-n) ≅
      ((shiftFunctor (Complex.{c, v, r} J R) n).op.prod (𝟭 _)) ⋙
        Functor.uncurry.obj (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)))
    (he : ∀ (n : ℤ) (L F : Complex.{c, v, r} J R),
      LeftFormula.{c, v, r} J R L F n ((e n).app (op L, F))) :
    ∃ z : ∀ n : ℤ, derivedInternalHomOfUniverses.{c, v, r, w} J R ⋙ shiftFunctor _ (-n) ≅
        ((shiftFunctor (D.{c, v, r, w} J R) n).op.prod (𝟭 _)) ⋙
          derivedInternalHomOfUniverses.{c, v, r, w} J R,
      (∀ (n : ℤ) (A M : D.{c, v, r, w} J R),
        (z n).hom.app (op A, M) = (sourceShift.{c, v, r, w} J R A n).hom.app M) ∧
      ∀ (n : ℤ) (L M : Complex.{c, v, r} J R),
        (z n).hom.app (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M) =
          ((bifunctorComparison.{c, v, r, w} J R).hom.app (op L, M))⟦-n⟧' ≫
            (DerivedCategory.Q.commShiftIso (-n)).inv.app
              (complexHom.{c, v, r} J R L
                ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj M)) ≫
            DerivedCategory.Q.map
              (((e n).app (op L,
                (WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj M)).hom) ≫
            (bifunctorComparison.{c, v, r, w} J R).inv.app (op (L⟦n⟧), M) ≫
            (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
              (Prod.mkHom (((DerivedCategory.Q.commShiftIso n).inv.app L).op) (𝟙 _)) := by
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let U := Functor.uncurry.obj
    (homComplexFunctor.{c, v, max c v r, max c v r} (R := R))
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  let η := ringedSiteHomAugmentation.{c, v, r} J R
  let α : U ⋙ Q ⟶ (Q.op.prod Q) ⋙ H :=
    Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) η) (U ⋙ Q) ≫
      (bifunctorComparison.{c, v, r, w} J R).inv
  choose z hz hfac using fun n ↦ sourceShiftDescent Q
    (HomologicalComplex.quasiIso (Modules.{c, v, r} J R) (.up ℤ)) U
    (WeilConjectures.coefficientHomResolution.{r, c, v} J R) η H
    (bifunctorComparison.{c, v, r, w} J R) n (e n)
  let S (P : D.{c, v, r, w} J R) (n : ℤ) :
      hom.{c, v, r, w} J R P ⋙ shiftFunctor _ (-n) ≅
        hom.{c, v, r, w} J R (P⟦n⟧) :=
    NatIso.ofComponents (fun M ↦ (z n).app (op P, M)) (by
      intro M M' f
      simpa only [Functor.comp_map, Functor.curry_obj_obj_map, Iso.app_hom,
        Functor.prod_map, Functor.op_map, unop_id, Functor.map_id, op_id,
        Functor.id_map] using (z n).hom.naturality (Prod.mkHom (𝟙 (op P)) f))
  have hnorm (n : ℤ) (P : D.{c, v, r, w} J R) (L F : Complex.{c, v, r} J R)
      (eP : Q.obj L ≅ P) :
      (Q.commShiftIso (-n)).hom.app (U.obj (op L, F)) ≫
          (α.app (op L, F) ≫ H.map (Prod.mkHom eP.inv.op (𝟙 _)))⟦-n⟧' ≫
            (S P n).hom.app (Q.obj F) =
        Q.map (((e n).app (op L, F)).hom) ≫ α.app (op (L⟦n⟧), F) ≫
          H.map (Prod.mkHom (((shiftFunctor _ n).map eP.inv) ≫
            (Q.commShiftIso n).inv.app L).op (𝟙 _)) := by
    have hn := (z n).hom.naturality (Prod.mkHom eP.inv.op (𝟙 (Q.obj F)))
    change (H.map (Prod.mkHom eP.inv.op (𝟙 (Q.obj F))))⟦-n⟧' ≫
        (z n).hom.app (op P, Q.obj F) =
      (z n).hom.app (op (Q.obj L), Q.obj F) ≫
        H.map (Prod.mkHom ((shiftFunctor _ n).map eP.inv).op (𝟙 (Q.obj F))) at hn
    change _ ≫ _ ≫ (z n).hom.app (op P, Q.obj F) = _
    calc
      _ = ((Q.commShiftIso (-n)).hom.app (U.obj (op L, F)) ≫
          (α.app (op L, F))⟦-n⟧' ≫ (z n).hom.app (op (Q.obj L), Q.obj F)) ≫
            H.map (Prod.mkHom ((shiftFunctor _ n).map eP.inv).op (𝟙 (Q.obj F))) := by
        simp only [Functor.map_comp, Category.assoc]
        rw [hn]
      _ = (Q.map (((e n).app (op L, F)).hom) ≫ α.app (op (L⟦n⟧), F) ≫
          H.map (Prod.mkHom (((Q.commShiftIso n).inv.app L).op) (𝟙 _))) ≫
            H.map (Prod.mkHom ((shiftFunctor _ n).map eP.inv).op (𝟙 (Q.obj F))) := by
        rw [hz n L F]
      _ = _ := by
        simp only [Category.assoc, ← H.map_comp, prod_comp, Category.id_comp, ← op_comp]
  have hS : LeftNormalization.{c, v, r, w} J R S := by
    intro P L F eP n
    refine ⟨(e n).app (op L, F), he n L F, ?_⟩
    exact hnorm n P L F eP
  have hEq : S = (leftShift_existsUnique.{c, v, r, w} J R).exists.choose :=
    (leftShift_existsUnique.{c, v, r, w} J R).unique hS
      (leftShift_existsUnique.{c, v, r, w} J R).exists.choose_spec
  refine ⟨z, ?_, hfac⟩
  intro n A M
  have hh := congrArg (fun V ↦ (V A n).hom.app M) hEq
  exact hh

private def modelShift (n : ℤ)
    (e : Functor.uncurry.obj
        (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) ⋙ shiftFunctor _ (-n) ≅
      ((shiftFunctor (Complex.{c, v, r} J R) n).op.prod (𝟭 _)) ⋙
        Functor.uncurry.obj (homComplexFunctor.{c, v, max c v r, max c v r} (R := R))) :
    (shiftFunctor (Complex.{c, v, r} J R) n).op ⋙ models.{c, v, r} J R ≅
      models.{c, v, r} J R ⋙
        (Functor.whiskeringRight _ _ _).obj (shiftFunctor _ (-n)) :=
  curryShiftOfCurried
    (homComplexFunctor.{c, v, max c v r, max c v r} (R := R))
    (shiftFunctor (Complex.{c, v, r} J R) n).op (shiftFunctor _ (-n))
    (WeilConjectures.coefficientHomResolution.{r, c, v} J R) e

private def strictShift (n : ℤ)
    (sigma : (shiftFunctor (Complex.{c, v, r} J R) n).op ⋙ models.{c, v, r} J R ≅
      models.{c, v, r} J R ⋙
        (Functor.whiskeringRight _ _ _).obj (shiftFunctor _ (-n))) :
    (shiftFunctor (Complex.{c, v, r} J R) n).op ⋙
        strictColimit.{c, v, r, w} (I := I) J R ≅
      strictColimit.{c, v, r, w} J R ⋙
        (Functor.whiskeringRight _ _ _).obj (shiftFunctor _ (-n)) :=
  Functor.isoWhiskerRight sigma
      (Functor.whiskeringRight I _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj (colim ⋙ DerivedCategory.Q)) ≪≫
    colimitShiftIso (models.{c, v, r} J R) DerivedCategory.Q (-n)

private theorem strictShift_app (n : ℤ)
    (sigma : (shiftFunctor (Complex.{c, v, r} J R) n).op ⋙ models.{c, v, r} J R ≅
      models.{c, v, r} J R ⋙
        (Functor.whiskeringRight _ _ _).obj (shiftFunctor _ (-n)))
    (L : Complex.{c, v, r} J R) (N : I ⥤ Complex.{c, v, r} J R) :
    ((strictShift.{c, v, r, w} J R n sigma).hom.app (op L)).app N =
      DerivedCategory.Q.map
        (colim.map (Functor.whiskerLeft N (sigma.hom.app (op L))) ≫
          (preservesColimitIso (shiftFunctor _ (-n))
            (N ⋙ (models.{c, v, r} J R).obj (op L))).inv) ≫
        (DerivedCategory.Q.commShiftIso (-n)).hom.app
          (colimit (N ⋙ (models.{c, v, r} J R).obj (op L))) := by
  change DerivedCategory.Q.map _ ≫
      (DerivedCategory.Q.map _ ≫ _) = _
  simp only [DerivedCategory.Q.map_comp, Category.assoc]
  rfl

private def targetShift (n : ℤ)
    (z : derivedInternalHomOfUniverses.{c, v, r, w} J R ⋙ shiftFunctor _ (-n) ≅
      ((shiftFunctor (D.{c, v, r, w} J R) n).op.prod (𝟭 _)) ⋙
        derivedInternalHomOfUniverses.{c, v, r, w} J R) :
    (shiftFunctor (D.{c, v, r, w} J R) n).op ⋙ target.{c, v, r, w} (I := I) J R ≅
      target.{c, v, r, w} J R ⋙
        (Functor.whiskeringRight _ _ _).obj (shiftFunctor _ (-n)) :=
  curryShift (derivedInternalHomOfUniverses.{c, v, r, w} J R)
    (shiftFunctor (D.{c, v, r, w} J R) n).op (shiftFunctor _ (-n))
    (colim ⋙ DerivedCategory.Q) z

private theorem target_map_app {A A' : (D.{c, v, r, w} J R)ᵒᵖ} (f : A ⟶ A')
    (N : I ⥤ Complex.{c, v, r} J R) :
    ((target.{c, v, r, w} J R).map f).app N =
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom f (𝟙 (DerivedCategory.Q.obj (colimit N)))) := rfl

private theorem targetShift_app (n : ℤ)
    (z : derivedInternalHomOfUniverses.{c, v, r, w} J R ⋙ shiftFunctor _ (-n) ≅
      ((shiftFunctor (D.{c, v, r, w} J R) n).op.prod (𝟭 _)) ⋙
        derivedInternalHomOfUniverses.{c, v, r, w} J R)
    (A : D.{c, v, r, w} J R) (N : I ⥤ Complex.{c, v, r} J R) :
    ((targetShift.{c, v, r, w} J R n z).hom.app (op A)).app N =
      z.inv.app (op A, DerivedCategory.Q.obj (colimit N)) := rfl

private theorem strictComparison_shift (n : ℤ)
    (e : Functor.uncurry.obj
        (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) ⋙ shiftFunctor _ (-n) ≅
      ((shiftFunctor (Complex.{c, v, r} J R) n).op.prod (𝟭 _)) ⋙
        Functor.uncurry.obj (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)))
    (z : derivedInternalHomOfUniverses.{c, v, r, w} J R ⋙ shiftFunctor _ (-n) ≅
      ((shiftFunctor (D.{c, v, r, w} J R) n).op.prod (𝟭 _)) ⋙
        derivedInternalHomOfUniverses.{c, v, r, w} J R)
    (hz : ∀ (L M : Complex.{c, v, r} J R),
      z.hom.app (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M) =
        ((bifunctorComparison.{c, v, r, w} J R).hom.app (op L, M))⟦-n⟧' ≫
          (DerivedCategory.Q.commShiftIso (-n)).inv.app
            (complexHom.{c, v, r} J R L
              ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj M)) ≫
          DerivedCategory.Q.map
            ((e.app (op L,
              (WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj M)).hom) ≫
          (bifunctorComparison.{c, v, r, w} J R).inv.app (op (L⟦n⟧), M) ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom (((DerivedCategory.Q.commShiftIso n).inv.app L).op) (𝟙 _)))
    (L : Complex.{c, v, r} J R) (N : I ⥤ Complex.{c, v, r} J R) :
    ((strictComparison.{c, v, r, w} J R).app (op (L⟦n⟧))).app N ≫
        ((target.{c, v, r, w} J R).map
          ((DerivedCategory.Q.commShiftIso n).inv.app L).op).app N ≫
        ((targetShift.{c, v, r, w} J R n z).hom.app
          (op (DerivedCategory.Q.obj L))).app N =
      ((strictShift.{c, v, r, w} J R n (modelShift.{c, v, r} J R n e)).hom.app
          (op L)).app N ≫
        (((strictComparison.{c, v, r, w} J R).app (op L)).app N)⟦-n⟧' := by
  let U := models.{c, v, r} J R
  let S := shiftFunctor (Complex.{c, v, r} J R) (-n)
  let σ := (modelShift.{c, v, r} J R n e).app (op L)
  have hs : colim.map (Functor.whiskerLeft N σ.hom) ≫
        (preservesColimitIso S (N ⋙ U.obj (op L))).inv ≫
        S.map (colimit.post N (U.obj (op L))) ≫ σ.inv.app (colimit N) =
      colimit.post N (U.obj (op (L⟦n⟧))) := by
    have h := congrArg (fun f ↦ f ≫ σ.inv.app (colimit N))
      (colimit_shift_square (U.obj (op (L⟦n⟧))) (U.obj (op L)) S σ N).symm
    simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using h
  rw [strictShift_app, strictComparison_app, strictComparison_app,
    targetShift_app, target_map_app]
  simpa only [U, S, σ, Iso.app_inv, Iso.app_hom, Category.assoc, Functor.comp_obj,
    Functor.prod_obj,
    Functor.whiskeringRight_obj_obj, Functor.curry_obj_obj_obj, target,
    strictColimit,
    models, Functor.whiskeringLeft_obj_obj, Functor.op_obj] using
    shiftComparisonSquare DerivedCategory.Q (-n)
    (colimit.post N (U.obj (op L)))
    (colimit.post N (U.obj (op (L⟦n⟧))))
    (colim.map (Functor.whiskerLeft N σ.hom) ≫
      (preservesColimitIso S (N ⋙ U.obj (op L))).inv)
    (σ.inv.app (colimit N))
    ((bifunctorComparison.{c, v, r, w} J R).app (op L, colimit N))
    ((bifunctorComparison.{c, v, r, w} J R).app (op (L⟦n⟧), colimit N))
    ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom (((DerivedCategory.Q.commShiftIso n).inv.app L).op) (𝟙 _)))
    (z.app (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj (colimit N)))
    (hz L (colimit N)) hs

private theorem strictColimit_inverts [IsFiltered I] :
    (HomologicalComplex.quasiIso (Modules.{c, v, r} J R) (.up ℤ)).op.IsInvertedBy
      (strictColimit.{c, v, r, w} (I := I) J R) := by
  let A := Modules.{c, v, r} J R
  let : IsGrothendieckAbelian.{max c v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  intro L L' f hf
  have : QuasiIso f.unop := hf
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  change IsIso (DerivedCategory.Q.map
    (colim.map (Functor.whiskerLeft N ((models.{c, v, r} J R).map f))))
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor A (.up ℤ) k
  let β := Functor.whiskerLeft N ((models.{c, v, r} J R).map f)
  have hb (i : I) : QuasiIso (β.app i) := by
    have : ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj
        (N.obj i)).IsKInjective := by
      dsimp only [WeilConjectures.coefficientHomResolution]
      exact CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} _ _
    change QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r}
      (R := R)).map f).app
        ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj (N.obj i)))
    simpa only [Quiver.Hom.op_unop, Functor.map_id, Category.comp_id] using
      quasiIso_homComplex_mapOfUniverses.{c, v, r}
        (𝟙 ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj (N.obj i)))
        f.unop
  have (i : I) : IsIso ((Functor.whiskerRight β H).app i) := by
    have := hb i
    change IsIso (HomologicalComplex.homologyMap (β.app i) k)
    infer_instance
  have : IsIso (Functor.whiskerRight β H) := NatIso.isIso_of_isIso_app _
  have hn := (preservesColimitNatIso H).hom.naturality β
  have he : H.map (colim.map β) =
      (preservesColimitIso H _).hom ≫ colim.map (Functor.whiskerRight β H) ≫
        (preservesColimitIso H _).inv := by
    simpa only [Functor.comp_map, Functor.whiskeringRight_obj_map,
      preservesColimitNatIso_hom_app, Category.assoc] using
      (Iso.eq_comp_inv _).mpr hn
  change IsIso (H.map (colim.map β))
  rw [he]
  infer_instance

private theorem sourceComparison [IsFiltered I] :
    ∃ (G : (D.{c, v, r, w} J R)ᵒᵖ ⥤
        (I ⥤ Complex.{c, v, r} J R) ⥤ D.{c, v, r, w} J R)
      (rho : DerivedCategory.Q.op ⋙ G ≅ strictColimit.{c, v, r, w} J R)
      (alpha : G ⟶ target.{c, v, r, w} J R),
      Functor.whiskerLeft DerivedCategory.Q.op alpha =
        rho.hom ≫ strictComparison.{c, v, r, w} J R := by
  let W := (HomologicalComplex.quasiIso (Modules.{c, v, r} J R) (.up ℤ)).op
  let G := Localization.lift (strictColimit.{c, v, r, w} (I := I) J R)
    (strictColimit_inverts.{c, v, r, w} J R) DerivedCategory.Q.op
  let rho : DerivedCategory.Q.op ⋙ G ≅ strictColimit.{c, v, r, w} J R :=
    Localization.fac _ (strictColimit_inverts.{c, v, r, w} J R) DerivedCategory.Q.op
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q.op W
    ((I ⥤ Complex.{c, v, r} J R) ⥤ D.{c, v, r, w} J R)
  exact ⟨G, rho, ff.preimage (rho.hom ≫ strictComparison.{c, v, r, w} J R),
    ff.map_preimage _⟩

/-- The actual Hom-colimit comparison descends in its source, commutes with every
source isomorphism, and commutes with the signed source shift, naturally in diagrams.
Source: Stacks 0A8X, 0A95, 08J7 and 08JC; the node's explicit cocone calculation
(blueprint: lem-sfb-rhom-colimit-source-transport).

Here G is the localized termwise-colimit model, rho identifies its complex-source
restriction, alpha is the canonical comparison, and t is its source-shift transport.
All of these are natural in the entire target diagram. The first equation fixes
alpha to Q(colimit.post), using the existing localization factorization. The second
is the source-isomorphism square; its vertical arrows are images of isomorphisms.
The third is the source-shift square with the already normalized signed sourceShift.
The final formula fixes t to the image under Q of the colimit of the signed chain
isomorphisms followed by the termwise colimit-shift identification, as a chain map;
LeftFormula specifies (-1)^(n*q).

Proof:
1. Put B_L(T)=Hom(L,J(T)) for the fixed functorial K-injective replacement.
The canonical map a_L=colimit.post N B_L is determined by a_L iota_i=B_L(u_i).
Precomposition commutes with postcomposition on each product component of Hom.
Testing on iota_i proves the source naturality square for every chain map.
2. Mod(R) is Grothendieck abelian with exact filtered colimits. Apply
src-weil-homology-preserves-exact-colimits in each integer degree: termwise
filtered colimits preserve objectwise quasi-isomorphisms without boundedness.
3. Stacks 0A95 (lem-pur-rhom-well-defined) makes B_v(T) a quasi-isomorphism
for a source quasi-isomorphism v. Step 2 does the same for its termwise colimit.
Thus L -> Q(a_L), as a functor into arrows of target-diagram functors, inverts
source quasi-isomorphisms. Localize it to obtain G, rho and alpha. The right
endpoint is the recorded derived internal Hom by its factorization comparison.
The localization universal property makes the representative identifications canonical.
4. Apply this localized functor to a source isomorphism and its inverse. This gives
the second equation and both inverse vertical maps, even without a chain-map lift.
5. On Hom degree q reindex p'=p+n and multiply by (-1)^(n*q). The inverse has
the same sign. The identity c_(q+1)=(-1)^n*c_q matches the cochain differential
on Hom(L[n],J(T)) with that on Hom(L,J(T))[-n]. These chain isomorphisms commute
with postcomposition by J(h); their sign depends only on n and q. This is precisely
LeftFormula and the normalization of sourceShift in the imported shift interface.
6. Take their colimit. In each degree the termwise colimit-shift identification
is the identity after reindexing; differentials agree with the same shift sign.
The last displayed formula is the image of this chain map. Testing the two chain-level
composites on the injections gives the shift square, and localizing retains it.
7. For a natural transformation of target diagrams, test on its colimit injections.
Functoriality of J, source precomposition and the signed reindexing commute with
these maps. All squares are therefore natural in the target diagram. Their vertical
maps are isomorphisms, so the horizontal maps are conjugate. No continuity or
boundedness assumption was used; filteredness was needed only in step 2. -/
theorem source_transport [IsFiltered I] :
    ∃ (G : (D.{c, v, r, w} J R)ᵒᵖ ⥤
        (I ⥤ Complex.{c, v, r} J R) ⥤ D.{c, v, r, w} J R)
      (rho : DerivedCategory.Q.op ⋙ G ≅ strictColimit.{c, v, r, w} J R)
      (alpha : G ⟶ target.{c, v, r, w} J R)
      (t : ∀ (A : D.{c, v, r, w} J R) (n : ℤ),
        G.obj (op (A⟦n⟧)) ≅ G.obj (op A) ⋙ shiftFunctor _ (-n)),
      (∀ (L : Complex.{c, v, r} J R) (N : I ⥤ Complex.{c, v, r} J R),
        (alpha.app (op (DerivedCategory.Q.obj L))).app N =
          (rho.hom.app (op L)).app N ≫
            DerivedCategory.Q.map (colimit.post N
              (WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L)) ≫
            (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L
              (colimit N)).inv) ∧
      (∀ (A A' : D.{c, v, r, w} J R) (e : A ≅ A')
        (N : I ⥤ Complex.{c, v, r} J R),
        (G.mapIso e.op).hom.app N ≫ (alpha.app (op A)).app N =
          (alpha.app (op A')).app N ≫
            ((target.{c, v, r, w} J R).mapIso e.op).hom.app N) ∧
      (∀ (A : D.{c, v, r, w} J R) (n : ℤ)
        (N : I ⥤ Complex.{c, v, r} J R),
        (alpha.app (op (A⟦n⟧))).app N ≫
            (sourceShift.{c, v, r, w} J R A n).inv.app
              (DerivedCategory.Q.obj (colimit N)) =
          (t A n).hom.app N ≫ ((alpha.app (op A)).app N)⟦-n⟧') ∧
      (∀ (L : Complex.{c, v, r} J R) (n : ℤ),
        ∃ sigma : WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R (L⟦n⟧) ≅
            WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L ⋙
              shiftFunctor _ (-n),
          (∀ M : Complex.{c, v, r} J R,
            LeftFormula.{c, v, r} J R L
              ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj M) n
              (sigma.symm.app M)) ∧
          ∀ N : I ⥤ Complex.{c, v, r} J R,
            (rho.inv.app (op (L⟦n⟧))).app N ≫
                (G.map ((DerivedCategory.Q.commShiftIso n).inv.app L).op).app N ≫
                (t (DerivedCategory.Q.obj L) n).hom.app N =
              DerivedCategory.Q.map (colim.map (Functor.whiskerLeft N sigma.hom) ≫
                  (preservesColimitIso (shiftFunctor (Complex.{c, v, r} J R) (-n))
                    (N ⋙ WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r}
                      J R L)).inv) ≫
                (DerivedCategory.Q.commShiftIso (-n)).hom.app
                  (colimit (N ⋙ WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r}
                    J R L)) ≫
                ((rho.inv.app (op L)).app N)⟦-n⟧') := by
  classical
  let A := Modules.{c, v, r} J R
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  obtain ⟨G, rho, alpha, hα⟩ := sourceComparison.{c, v, r, w} (I := I) J R
  choose e he using fun n ↦ ordinaryShift.{c, v, r, w} J R n
  obtain ⟨z, hnorm, hz⟩ := derivedShifts.{c, v, r, w} J R e he
  let σ (n : ℤ) := modelShift.{c, v, r} J R n (e n)
  let b (n : ℤ) := strictShift.{c, v, r, w} (I := I) J R n (σ n)
  let T (n : ℤ) :=
    (Functor.whiskeringRight (I ⥤ Complex.{c, v, r} J R)
      (D.{c, v, r, w} J R) (D.{c, v, r, w} J R)).obj (shiftFunctor _ (-n))
  choose t ht using fun n ↦ descendShiftIso Q W
    (strictColimit.{c, v, r, w} J R) G rho (T n) n (b n)
  have hshift (n : ℤ) :
      Functor.whiskerLeft (shiftFunctor (D.{c, v, r, w} J R) n).op alpha ≫
          (targetShift.{c, v, r, w} J R n (z n)).hom =
        (t n).hom ≫ Functor.whiskerRight alpha (T n) := by
    apply Localization.natTrans_ext Q.op W.op
    intro L₀
    let L := L₀.unop
    change _ = _
    ext N
    let q := ((Q.commShiftIso n).inv.app L).op
    have hn := NatTrans.congr_app (alpha.naturality q) N
    change (G.map q).app N ≫ (alpha.app (op ((Q.obj L)⟦n⟧))).app N =
      (alpha.app (op (Q.obj (L⟦n⟧)))).app N ≫
        ((target.{c, v, r, w} J R).map q).app N at hn
    have ha (M : Complex.{c, v, r} J R) :
        (alpha.app (op (Q.obj M))).app N = (rho.hom.app (op M)).app N ≫
          ((strictComparison.{c, v, r, w} J R).app (op M)).app N :=
      NatTrans.congr_app (NatTrans.congr_app hα (op M)) N
    have hρ (M : Complex.{c, v, r} J R) :
        (rho.inv.app (op M)).app N ≫ (rho.hom.app (op M)).app N = 𝟙 _ :=
      NatTrans.congr_app (rho.inv_hom_id_app (op M)) N
    have htN := NatTrans.congr_app (ht n L) N
    dsimp only [NatTrans.comp_app, T, Functor.whiskeringRight_obj_map,
      Functor.whiskerRight_app] at htN
    apply (cancel_epi ((rho.inv.app (op (L⟦n⟧))).app N ≫ (G.map q).app N)).mp
    change ((rho.inv.app (op (L⟦n⟧))).app N ≫ (G.map q).app N) ≫
        ((alpha.app (op ((Q.obj L)⟦n⟧))).app N ≫
          ((targetShift.{c, v, r, w} J R n (z n)).hom.app (op (Q.obj L))).app N) =
      ((rho.inv.app (op (L⟦n⟧))).app N ≫ (G.map q).app N) ≫
        ((t n).hom.app (op (Q.obj L))).app N ≫ ((alpha.app (op (Q.obj L))).app N)⟦-n⟧'
    calc
      _ = (((rho.inv.app (op (L⟦n⟧))).app N ≫
          (alpha.app (op (Q.obj (L⟦n⟧)))).app N) ≫
            ((target.{c, v, r, w} J R).map q).app N ≫
              ((targetShift.{c, v, r, w} J R n (z n)).hom.app
                (op (Q.obj L))).app N) := by
        simp only [Category.assoc]
        simpa only [Category.assoc] using congrArg (fun f ↦ (rho.inv.app (op (L⟦n⟧))).app N ≫ f ≫
          ((targetShift.{c, v, r, w} J R n (z n)).hom.app (op (Q.obj L))).app N) hn
      _ = ((strictComparison.{c, v, r, w} J R).app (op (L⟦n⟧))).app N ≫
          ((target.{c, v, r, w} J R).map q).app N ≫
            ((targetShift.{c, v, r, w} J R n (z n)).hom.app
              (op (Q.obj L))).app N := by
        rw [ha (L⟦n⟧)]
        simp only [← Category.assoc, hρ, Category.id_comp]
      _ = ((b n).hom.app (op L)).app N ≫
          (((strictComparison.{c, v, r, w} J R).app (op L)).app N)⟦-n⟧' :=
        strictComparison_shift.{c, v, r, w} J R n (e n) (z n) (hz n) L N
      _ = ((b n).hom.app (op L)).app N ≫
          (((rho.inv.app (op L)).app N ≫
            (alpha.app (op (Q.obj L))).app N))⟦-n⟧' := by
        rw [ha L]
        simp only [← Category.assoc, hρ, Category.id_comp]
      _ = (((b n).hom.app (op L)).app N ≫
          ((rho.inv.app (op L)).app N)⟦-n⟧') ≫
            ((alpha.app (op (Q.obj L))).app N)⟦-n⟧' := by
        rw [Functor.map_comp, Category.assoc]
      _ = _ := by
        rw [← htN]
        simp only [q, Category.assoc]
  refine ⟨G, rho, alpha, fun A n ↦ (t n).app (op A), ?_, ?_, ?_, ?_⟩
  · intro L N
    have h := NatTrans.congr_app (NatTrans.congr_app hα (op L)) N
    dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app] at h
    calc
      _ = (rho.hom.app (op L)).app N ≫
          ((strictComparison.{c, v, r, w} J R).app (op L)).app N := h
      _ = _ := by
        dsimp only [strictComparison, NatTrans.comp_app, colimitComparison]
        rw [diagramComparison_app]
        rfl
  · intro A A' e N
    exact NatTrans.congr_app (alpha.naturality e.op.hom) N
  · intro A n N
    have hh := NatTrans.congr_app (NatTrans.congr_app (hshift n) (op A)) N
    have heq : (z n).app (op A, DerivedCategory.Q.obj (colimit N)) =
        (sourceShift.{c, v, r, w} J R A n).app
          (DerivedCategory.Q.obj (colimit N)) := Iso.ext (hnorm n A _)
    change _ ≫ ((z n).app (op A, DerivedCategory.Q.obj (colimit N))).inv = _ at hh
    rw [heq] at hh
    exact hh
  · intro L n
    refine ⟨(σ n).app (op L), ?_, ?_⟩
    · intro M
      exact he n L ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj M)
    · intro N
      have hh := NatTrans.congr_app (ht n L) N
      dsimp only [NatTrans.comp_app] at hh
      change _ = ((strictShift.{c, v, r, w} J R n (σ n)).hom.app (op L)).app N ≫
        ((rho.inv.app (op L)).app N)⟦-n⟧' at hh
      rw [strictShift_app] at hh
      simpa only [Q, models, Functor.comp_obj, Functor.op_obj,
        Functor.whiskeringLeft_obj_obj, WeilConjectures.SfbHomFilteredColimit.homFixed,
        Iso.app_hom, Category.assoc] using hh

end CategoryTheory.RingedHomColimitTransport
