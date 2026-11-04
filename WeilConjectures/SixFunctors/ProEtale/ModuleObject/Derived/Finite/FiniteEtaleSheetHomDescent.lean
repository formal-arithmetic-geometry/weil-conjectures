/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleTraceFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleSplitHomDescent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteEtaleLocalTransposeCompatible

/-! # Descent of module morphisms along the sheets of finite etale splitting charts

For a finite etale map `p : U ⟶ X`, the sheets of all finite splitting charts of `p` cover `U`.
Module maps on all these sheets which agree on every common weakly etale refinement glue to a
module map on `U`. This is the source-side analogue of `finiteEtaleSplitHom_exists`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarLowerStarAdjunction
  ProEtale.upperStar ProEtale.upperStarComp

/-- The sheets of a splitting chart of an etale map are weakly etale. -/
instance FiniteEtaleModuleChart.weaklyEtale_sheet {X U : Scheme.{u}} {p : U ⟶ X} [Etale p]
    (c : FiniteEtaleModuleChart p) (j : Fin c.degree) : WeaklyEtale (c.sheet j) := by
  have : WeaklyEtale (c.sheet j ≫ p) := by
    rw [c.over j]
    infer_instance
  exact WeaklyEtale.of_comp (c.sheet j) p

/-- The sheets of etale splitting charts through every point form an etale cover. -/
private theorem sheet_chart_cover {X U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] :
    ∃ (c : U → FiniteEtaleModuleChart p) (j : ∀ u, Fin (c u).degree),
      Presieve.ofArrows (fun u ↦ (c u).base) (fun u ↦ (c u).sheet (j u)) ∈
        Scheme.proetalePrecoverage U := by
  choose c j y hc hy using FiniteEtaleModuleChart.exists_sheet_apply_eq p
  refine ⟨c, j, ?_⟩
  apply Scheme.etalePrecoverage_le_proetalePrecoverage
  refine (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun u ↦ ⟨u, y u, hy u⟩, fun u ↦ ?_⟩
  have := hc u
  have : Etale ((c u).sheet (j u) ≫ p) := by
    rw [(c u).over (j u)]
    infer_instance
  exact Etale.of_comp ((c u).sheet (j u)) p

/-- Glue literal restrictions on all sheets of all charts by the sheaf of morphisms. -/
private theorem sheet_chart_glue_sheaf
    {X U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p]
    (F G : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
    (ψ : ∀ (c : FiniteEtaleModuleChart p) (j : Fin c.degree),
      (ProEtale.localizationRestriction Ab.{u + 1} (c.sheet j) inferInstance).obj F ⟶
        (ProEtale.localizationRestriction Ab.{u + 1} (c.sheet j) inferInstance).obj G)
    (hψ : ∀ (c : FiniteEtaleModuleChart p) (j : Fin c.degree) (k : FiniteEtaleModuleChart p)
      (l : Fin k.degree) (T : U.ProEt)
      (a : T.left ⟶ c.base) (b : T.left ⟶ k.base)
      (ha : a ≫ c.sheet j = T.hom) (hb : b ≫ k.sheet l = T.hom),
      F.obj.map (ProEtale.overMapIso (c.sheet j) inferInstance T a ha).hom.op ≫
          (ψ c j).hom.app (op _) ≫
          G.obj.map (ProEtale.overMapIso (c.sheet j) inferInstance T a ha).inv.op =
        F.obj.map (ProEtale.overMapIso (k.sheet l) inferInstance T b hb).hom.op ≫
          (ψ k l).hom.app (op _) ≫
          G.obj.map (ProEtale.overMapIso (k.sheet l) inferInstance T b hb).inv.op) :
    ∃ φ : F ⟶ G, ∀ c j,
      (ProEtale.localizationRestriction Ab.{u + 1} (c.sheet j) inferInstance).map φ = ψ c j := by
  classical
  let I := Σ c : FiniteEtaleModuleChart p, Fin c.degree
  let H := presheafHom F.obj G.obj
  let V' : I → U.ProEt := fun x ↦ MorphismProperty.Over.mk ⊤ (x.1.sheet x.2) inferInstance
  let top : U.ProEt := MorphismProperty.Over.mk ⊤ (𝟙 U) inferInstance
  let π : ∀ x, V' x ⟶ top := fun x ↦
    MorphismProperty.Over.homMk (x.1.sheet x.2) (Category.comp_id _) trivial
  have hw : ∀ x (T : Over (V' x)), T.hom.left ≫ x.1.sheet x.2 = T.left.hom :=
    fun x T ↦ MorphismProperty.Over.w T.hom
  let Φ : ∀ x : I, Over (V' x) ⥤ x.1.base.ProEt := fun x ↦
    { obj T := MorphismProperty.Over.mk ⊤ T.hom.left
        (MorphismProperty.of_postcomp _ _ _ (inferInstance : WeaklyEtale (x.1.sheet x.2)) (by
          rw [hw x T]; exact T.left.prop))
      map g := MorphismProperty.Over.homMk g.left.left
        (congrArg (fun f ↦ f.left) (Over.w g)) trivial }
  let κ : ∀ x : I, Φ x ⋙ MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale (x.1.sheet x.2)) ≅ Over.forget (V' x) :=
    fun x ↦ NatIso.ofComponents (fun T ↦
      ProEtale.overMapIso (x.1.sheet x.2) inferInstance T.left T.hom.left (hw x T))
      (fun g ↦ by ext; simp [ProEtale.overMapIso, Φ])
  let s : ∀ x : I, H.obj (op (V' x)) := fun x ↦
    (Functor.isoWhiskerRight (NatIso.op (κ x)) F.obj).hom ≫
      Functor.whiskerLeft (Φ x).op (ψ x.1 x.2).hom ≫
        (Functor.isoWhiskerRight (NatIso.op (κ x)) G.obj).inv
  have hs : Presieve.Arrows.Compatible H π s := by
    intro x y Z a b _
    refine NatTrans.ext (funext fun T ↦ ?_)
    exact hψ x.1 x.2 y.1 y.2 T.unop.left _ _
      (hw x ((Over.map a).obj T.unop)) (hw y ((Over.map b).obj T.unop))
  have hH : Presheaf.IsSheaf (Scheme.ProEt.topology U) H :=
    Presheaf.IsSheaf.hom F.obj G.obj G.property
  have hcov : Sieve.generate (Presieve.ofArrows V' π) ∈
      Scheme.ProEt.topology U top := by
    obtain ⟨c, j, hcj⟩ := sheet_chart_cover p
    have hsmall : Presieve.ofArrows (fun u ↦ V' ⟨c u, j u⟩) (fun u ↦ π ⟨c u, j u⟩) ∈
        Scheme.ProEt.precoverage U top := by
      rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
      exact hcj
    apply Scheme.ProEt.mem_topology_iff.mpr
    refine ⟨_, hsmall, ?_⟩
    rintro Z f ⟨u⟩
    exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk (⟨c u, j u⟩ : I))
  have hsf : (Presieve.ofArrows V' π).IsSheafFor H := by
    rw [Presieve.isSheafFor_iff_generate]
    exact (isSheaf_iff_isSheaf_of_type _ _).mp hH _ hcov
  obtain ⟨t, ht, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf s hs
  let toTop : ∀ V : U.ProEt, V ⟶ top := fun V ↦
    MorphismProperty.Over.homMk V.hom (Category.comp_id _) trivial
  have htop : ∀ {V : U.ProEt} (f : V ⟶ top), f = toTop V := fun f ↦
    MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).symm.trans (MorphismProperty.Over.w f))
  let σ : H.sections := ⟨fun V ↦ H.map (toTop V.unop).op t, fun {V V'} f ↦ by
    simp only [← Functor.map_comp_apply]
    rw [show (toTop V.unop).op ≫ f = (f.unop ≫ toTop V.unop).op from rfl,
      htop (f.unop ≫ toTop V.unop)]⟩
  refine ⟨⟨presheafHomSectionsEquiv _ _ σ⟩, ?_⟩
  intro c j
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  let g₀ : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (c.sheet j))).obj W.unop ⟶
      V' ⟨c, j⟩ :=
    MorphismProperty.Over.homMk W.unop.hom rfl trivial
  have h := congrArg (fun α ↦ α.app (op (Over.mk g₀))) (ht ⟨c, j⟩)
  have hκ : ProEtale.overMapIso (c.sheet j) inferInstance _ g₀.left
      (hw ⟨c, j⟩ (Over.mk g₀)) = Iso.refl _ := by ext; rfl
  dsimp only [s] at h
  simp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.op_hom, NatIso.op_inv,
    NatTrans.op_app] at h
  have h₁ : (κ ⟨c, j⟩).hom.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.hom hκ
  have h₂ : (κ ⟨c, j⟩).inv.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.inv hκ
  rw [h₁, h₂] at h
  erw [op_id, F.obj.map_id, G.obj.map_id, Category.id_comp, Category.comp_id] at h
  refine Eq.trans ?_ h
  change t.app (op (Over.mk (𝟙 _ ≫ toTop _))) = t.app (op (Over.mk (g₀ ≫ π ⟨c, j⟩)))
  rw [htop (𝟙 _ ≫ toTop _), htop (g₀ ≫ π ⟨c, j⟩)]

/-- The inverse images on all sheets jointly detect equality of sheaf maps. -/
private theorem sheet_chart_sheaf_hom_ext
    {X U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p]
    {F G : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}} (f g : F ⟶ G)
    (h : ∀ (c : FiniteEtaleModuleChart p) (j : Fin c.degree),
      (ProEtale.upperStar Ab.{u + 1} (c.sheet j)).map f =
        (ProEtale.upperStar Ab.{u + 1} (c.sheet j)).map g) : f = g := by
  classical
  obtain ⟨c, j, hcover⟩ := sheet_chart_cover p
  have hj : JointlyFaithful (fun u ↦ ProEtale.upperStar Ab.{u + 1} ((c u).sheet (j u))) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro M N φ hφ
    apply ProEtale.isIso_of_isIso_localizationRestriction Ab.{u + 1} φ
      (fun u ↦ (c u).sheet (j u)) hcover
    intro u
    exact (NatIso.isIso_map_iff (ProEtale.upperStarIsoLocalizationRestriction
      Ab.{u + 1} ((c u).sheet (j u)) inferInstance) φ).mp (hφ u)
  exact hj.map_injective (fun u ↦ h (c u) (j u))

open CategoryTheory.MonoidalCategory

/-- A sheaf map on `U` that is locally a module map on all sheets is a module map. -/
private theorem sheet_chart_linear
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (Q P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (d : ∀ (c : FiniteEtaleModuleChart p) (j : Fin c.degree),
      (upperStar Λ (c.sheet j)).obj Q ⟶ (upperStar Λ (c.sheet j)).obj P)
    (φ : Q.X ⟶ P.X)
    (hφ : ∀ c j, (ProEtale.localizationRestriction Ab.{u + 1} (c.sheet j) inferInstance).map φ =
      (moduleLocalization Λ (c.sheet j)).inv.app Q ≫ (d c j).hom ≫
        (moduleLocalization Λ (c.sheet j)).hom.app P) :
    CategoryTheory.IsModHom (condensedRingObj Λ U) φ := by
  classical
  unfold upperStar at d
  constructor
  apply sheet_chart_sheaf_hom_ext p
  intro c j
  let F := ProEtale.upperStar Ab.{u + 1} (c.sheet j)
  let α := ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} (c.sheet j) inferInstance
  let R := condensedRingObj Λ U
  let A := condensedPullbackHom Λ (c.sheet j)
  let E := Mod.extendScalars A
  let e := Mod.extendScalarsIsoComapInv A
  have : (Mod.comap (D := Sheaf (Scheme.ProEt.topology c.base) Ab.{u + 1})
      (asIso A).inv).IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso A).inverse.IsEquivalence
  have : E.IsEquivalence := Functor.isEquivalence_of_iso e.symm
  let δ : (F.mapMod R).obj Q ⟶ (F.mapMod R).obj P := E.preimage (d c j)
  have hδ : F.map φ = δ.hom := by
    have he := congrArg Mod.Hom.hom (e.hom.naturality δ)
    change (E.map δ).hom ≫ (e.hom.app ((F.mapMod R).obj P)).hom =
      (e.hom.app ((F.mapMod R).obj Q)).hom ≫ δ.hom at he
    have hmap : E.map δ = d c j := E.map_preimage (d c j)
    rw [hmap] at he
    have hδ₀ : (e.inv.app ((F.mapMod R).obj Q)).hom ≫ (d c j).hom ≫
        (e.hom.app ((F.mapMod R).obj P)).hom = δ.hom := by
      rw [he, ← Category.assoc]
      have hid := congrArg Mod.Hom.hom (e.inv_hom_id_app ((F.mapMod R).obj Q))
      rw [Mod.comp_hom'] at hid
      rw [hid]
      exact Category.id_comp _
    have hc := hφ c j
    dsimp only [moduleLocalization, profinitePointModuleForgetPullbackIso, Iso.trans_inv,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj, Mod.forget] at hc
    erw [Category.assoc] at hc
    change (ProEtale.localizationRestriction Ab.{u + 1} (c.sheet j) inferInstance).map φ =
      α.inv.app Q.X ≫ (e.inv.app ((F.mapMod R).obj Q)).hom ≫ (d c j).hom ≫
        (e.hom.app ((F.mapMod R).obj P)).hom ≫ α.hom.app P.X at hc
    have hn := α.hom.naturality φ
    rw [hc, Iso.hom_inv_id_app_assoc, reassoc_of% hδ₀] at hn
    exact (cancel_mono (α.hom.app P.X)).mp hn
  exact map_action_identity F Q P φ δ hδ

/-- The normalized sheet maps are a matching family of sheaf morphisms. -/
private theorem sheet_chart_compatible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X) [Etale p]
    (Q P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (d : ∀ (c : FiniteEtaleModuleChart p) (j : Fin c.degree),
      (upperStar Λ (c.sheet j)).obj Q ⟶ (upperStar Λ (c.sheet j)).obj P)
    (hd : ∀ (c₁ : FiniteEtaleModuleChart p) (j₁ : Fin c₁.degree)
      (c₂ : FiniteEtaleModuleChart p) (j₂ : Fin c₂.degree) (Z : Scheme.{u})
      (a : Z ⟶ c₁.base) (b : Z ⟶ c₂.base) [WeaklyEtale a] [WeaklyEtale b] (k : Z ⟶ U)
      (ha : k = a ≫ c₁.sheet j₁) (hb : k = b ≫ c₂.sheet j₂),
      ((eqToIso (congrArg (upperStar Λ) ha)) ≪≫ upperStarComp Λ a (c₁.sheet j₁)).hom.app Q ≫
          (upperStar Λ a).map (d c₁ j₁) ≫
          ((eqToIso (congrArg (upperStar Λ) ha)) ≪≫ upperStarComp Λ a (c₁.sheet j₁)).inv.app P =
        ((eqToIso (congrArg (upperStar Λ) hb)) ≪≫ upperStarComp Λ b (c₂.sheet j₂)).hom.app Q ≫
          (upperStar Λ b).map (d c₂ j₂) ≫
          ((eqToIso (congrArg (upperStar Λ) hb)) ≪≫ upperStarComp Λ b (c₂.sheet j₂)).inv.app P)
    (c : FiniteEtaleModuleChart p) (j : Fin c.degree) (k : FiniteEtaleModuleChart p)
    (l : Fin k.degree) (T : U.ProEt) (a : T.left ⟶ c.base) (b : T.left ⟶ k.base)
    (ha : a ≫ c.sheet j = T.hom) (hb : b ≫ k.sheet l = T.hom) :
    Q.X.obj.map (ProEtale.overMapIso (c.sheet j) inferInstance T a ha).hom.op ≫
        ((moduleLocalization Λ (c.sheet j)).inv.app Q ≫ (d c j).hom ≫
          (moduleLocalization Λ (c.sheet j)).hom.app P).hom.app (op _) ≫
        P.X.obj.map (ProEtale.overMapIso (c.sheet j) inferInstance T a ha).inv.op =
      Q.X.obj.map (ProEtale.overMapIso (k.sheet l) inferInstance T b hb).hom.op ≫
        ((moduleLocalization Λ (k.sheet l)).inv.app Q ≫ (d k l).hom ≫
          (moduleLocalization Λ (k.sheet l)).hom.app P).hom.app (op _) ≫
        P.X.obj.map (ProEtale.overMapIso (k.sheet l) inferInstance T b hb).inv.op := by
  have : WeaklyEtale (a ≫ c.sheet j) := ha ▸ T.prop
  have : WeaklyEtale a := WeaklyEtale.of_comp a (c.sheet j)
  have : WeaklyEtale (b ≫ k.sheet l) := hb ▸ T.prop
  have : WeaklyEtale b := WeaklyEtale.of_comp b (k.sheet l)
  have : WeaklyEtale T.hom := T.prop
  have h := hd c j k l T.left a b T.hom ha.symm hb.symm
  have h' := normalize_map_eq (upperStar (X := T.left) (Y := U) Λ T.hom)
    (Mod.forget (condensedRingObj Λ U) ⋙
      ProEtale.localizationRestriction (U := U) (V := T.left) Ab.{u + 1} T.hom T.prop)
    (Mod.forget (condensedRingObj Λ T.left))
    (moduleLocalization (X := U) (Y := T.left) Λ T.hom) Q P h
  dsimp only [Functor.comp_obj, Mod.forget] at h'
  have hov := (moduleLocalization_conj' Λ a (c.sheet j) T.hom ha.symm Q P (d c j)).symm.trans
    (h'.trans (moduleLocalization_conj' Λ b (k.sheet l) T.hom hb.symm Q P (d k l)))
  have h₁ := localization_component (c.sheet j) Q.X P.X
    ((moduleLocalization Λ (c.sheet j)).inv.app Q ≫ (d c j).hom ≫
      (moduleLocalization Λ (c.sheet j)).hom.app P) T a ha
  have h₂ := localization_component (k.sheet l) Q.X P.X
    ((moduleLocalization Λ (k.sheet l)).inv.app Q ≫ (d k l).hom ≫
      (moduleLocalization Λ (k.sheet l)).hom.app P) T b hb
  dsimp only at h₁ h₂
  rw [hov] at h₁
  exact h₁.symm.trans h₂

/-- **Descent of module maps along the sheets of finite splitting charts.** Module maps on all
sheets of all finite splitting charts of a finite etale map, whose pullbacks to every weakly
etale scheme mapping compatibly to two sheets agree, are the pullbacks of a module map.
Source: Stacks Project, Tags 03EM, 04TQ and 04HN.
(blueprint: new-det-sp-native-finite-etale-local-transpose-gluing) -/
theorem finiteEtaleSheetHom_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (Q P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (d : ∀ (c : FiniteEtaleModuleChart p) (j : Fin c.degree),
      (upperStar Λ (c.sheet j)).obj Q ⟶ (upperStar Λ (c.sheet j)).obj P)
    (hd : ∀ (c₁ : FiniteEtaleModuleChart p) (j₁ : Fin c₁.degree)
      (c₂ : FiniteEtaleModuleChart p) (j₂ : Fin c₂.degree) (Z : Scheme.{u})
      (a : Z ⟶ c₁.base) (b : Z ⟶ c₂.base) [WeaklyEtale a] [WeaklyEtale b] (k : Z ⟶ U)
      (ha : k = a ≫ c₁.sheet j₁) (hb : k = b ≫ c₂.sheet j₂),
      ((eqToIso (congrArg (upperStar Λ) ha)) ≪≫ upperStarComp Λ a (c₁.sheet j₁)).hom.app Q ≫
          (upperStar Λ a).map (d c₁ j₁) ≫
          ((eqToIso (congrArg (upperStar Λ) ha)) ≪≫ upperStarComp Λ a (c₁.sheet j₁)).inv.app P =
        ((eqToIso (congrArg (upperStar Λ) hb)) ≪≫ upperStarComp Λ b (c₂.sheet j₂)).hom.app Q ≫
          (upperStar Λ b).map (d c₂ j₂) ≫
          ((eqToIso (congrArg (upperStar Λ) hb)) ≪≫ upperStarComp Λ b (c₂.sheet j₂)).inv.app P) :
    ∃ f : Q ⟶ P, ∀ c j, (upperStar Λ (c.sheet j)).map f = d c j := by
  classical
  obtain ⟨φ, hφ⟩ := sheet_chart_glue_sheaf p Q.X P.X (fun c j ↦
    (moduleLocalization Λ (c.sheet j)).inv.app Q ≫ (d c j).hom ≫
      (moduleLocalization Λ (c.sheet j)).hom.app P)
    (sheet_chart_compatible Λ p Q P d hd)
  have : CategoryTheory.IsModHom (condensedRingObj Λ U) φ :=
    sheet_chart_linear Λ p Q P d φ hφ
  let f : Q ⟶ P := ⟨φ⟩
  refine ⟨f, fun c j ↦ ?_⟩
  apply (Mod.forget (condensedRingObj Λ c.base)).map_injective
  have hn := (moduleLocalization Λ (c.sheet j)).hom.naturality f
  change ((upperStar Λ (c.sheet j)).map f).hom ≫ (moduleLocalization Λ (c.sheet j)).hom.app P =
    (moduleLocalization Λ (c.sheet j)).hom.app Q ≫
      (ProEtale.localizationRestriction Ab.{u + 1} (c.sheet j) inferInstance).map φ at hn
  rw [hφ c j] at hn
  simp only [Iso.hom_inv_id_app_assoc] at hn
  exact (cancel_mono ((moduleLocalization Λ (c.sheet j)).hom.app P)).mp hn

end AlgebraicGeometry.ProEtale.CondensedRing
