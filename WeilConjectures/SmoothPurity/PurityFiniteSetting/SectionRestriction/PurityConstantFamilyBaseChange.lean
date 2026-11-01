/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionConstantTrivialization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence

/-! # Reading constant line families after base change

Source: DNC family constancy, base-change normalization
(blueprint: lem-pur-constant-family-base-change).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionRestriction

section Coherence
variable (P : PurityFiniteSetting.{u})

private noncomputable def compAlong {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (e : fg = f ≫ g) :=
  ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) e ≪≫
    ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g

private theorem compAlong_assoc {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z)
    (fgh : W ⟶ Z) (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient))) :
    (compAlong P f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map
          ((compAlong P g h gh hgh).hom.app K) =
      (compAlong P fg h fgh hfgh).hom.app K ≫
        (compAlong P f g fg hfg).hom.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).leftDerivedFunctor.obj K)
          := by
  subst fg gh fgh
  simpa only [compAlong, Iso.trans_hom, NatTrans.comp_app,
    ProEtale.leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Functor.map_id, Category.comp_id] using
    (ProEtale.leftDerivedUpperStarComp_assoc_app f g h K).symm

private theorem compAlong_unit_left {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (compAlong P (𝟙 X) f f (Category.id_comp f).symm).hom.app K ≫
      (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) X).hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj K) =
        𝟙 _ := by
  dsimp only [compAlong, Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, ProEtale.leftDerivedUpperStarComp_id_left_app,
    ProEtale.leftDerivedUpperStarCongr_hom_app_trans,
    ProEtale.leftDerivedUpperStarCongr_hom_app_self]

private theorem compAlong_unit_right {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (compAlong P f (𝟙 Y) f (Category.comp_id f).symm).hom.app K ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map
        ((ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) Y).hom.app K) =
        𝟙 _ := by
  dsimp only [compAlong, Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, ProEtale.leftDerivedUpperStarComp_id_right_app,
    ProEtale.leftDerivedUpperStarCongr_hom_app_trans,
    ProEtale.leftDerivedUpperStarCongr_hom_app_self]

private noncomputable def sectionAlong {B D : Scheme.{u}} (a : D ⟶ B) (i : B ⟶ D)
    (h : i ≫ a = 𝟙 B) :=
  (compAlong P i a (𝟙 B) h.symm).symm ≪≫
    ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B

private theorem section_coherence {B B' D D' : Scheme.{u}} (b : B' ⟶ B)
    (a : D ⟶ B) (a' : D' ⟶ B') (v : D' ⟶ D) (i : B ⟶ D) (i' : B' ⟶ D')
    (hv : v ≫ a = a' ≫ b) (hi : i' ≫ v = b ≫ i)
    (h : i ≫ a = 𝟙 B) (h' : i' ≫ a' = 𝟙 B')
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient))) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i').leftDerivedFunctor.map
        ((compAlong P v a (v ≫ a) rfl).inv.app K ≫
          (compAlong P a' b (v ≫ a) hv).hom.app K) ≫
        (sectionAlong P a' i' h').hom.app _ =
      ((compAlong P i' v (i' ≫ v) rfl).inv.app _ ≫
          (compAlong P b i (i' ≫ v) hi).hom.app _) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.map
          ((sectionAlong P a i h).hom.app K) := by
  have hb : b = i' ≫ v ≫ a := by rw [hv, ← Category.assoc, h', Category.id_comp]
  have A1 := compAlong_assoc P i' a' b (𝟙 B') (v ≫ a) b h'.symm hv
    (Category.id_comp b).symm K
  have A2 := compAlong_assoc P i' v a (i' ≫ v) (v ≫ a) b rfl rfl
    (by rw [hb, Category.assoc]) K
  have A3 := compAlong_assoc P b i a (i' ≫ v) (𝟙 B) b hi h.symm
    (by rw [hb, Category.assoc]) K
  have UL := compAlong_unit_left P b K
  have UR := compAlong_unit_right P b K
  rw [← cancel_epi ((compAlong P i' (v ≫ a) b hb).hom.app K ≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i').leftDerivedFunctor.map
      ((compAlong P v a (v ≫ a) rfl).hom.app K))]
  simp only [sectionAlong, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% A1, Iso.hom_inv_id_app_assoc, UL,
    reassoc_of% A2, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% A3, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, UR]

private theorem line_projection_coherence {B B' : Scheme.{u}} (b : B' ⟶ B)
    (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (i' : B' ⟶ AffineSpace (ULift.{u} (Fin 1)) B')
    (hi : i' ≫ AffineSpace.map (ULift.{u} (Fin 1)) b = b ≫ i)
    (h : i ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) = 𝟙 B)
    (h' : i' ≫ (AffineSpace (ULift.{u} (Fin 1)) B' ↘ B') = 𝟙 B')
    (C : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient))) :
    let a := (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)
    let a' := (AffineSpace (ULift.{u} (Fin 1)) B' ↘ B')
    let v := AffineSpace.map (ULift.{u} (Fin 1)) b
    let A := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor
    let U := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor
    let E' := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i').leftDerivedFunctor
    let M := (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) v a).symm ≪≫
      ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.map_over b) ≪≫
      ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) a' b
    endpointPull P b i i' hi (A.obj C) ≪≫ E'.mapIso (M.app C) ≪≫
        (lineCounit P B' i' h').app (U.obj C) = U.mapIso ((lineCounit P B i h).app C) := by
  dsimp only
  apply Iso.ext
  apply (cancel_epi (endpointPull P b i i' hi _).inv).mp
  simp only [Iso.trans_hom, Iso.inv_hom_id_assoc]
  have H := section_coherence P b
    (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)
    (AffineSpace (ULift.{u} (Fin 1)) B' ↘ B')
    (AffineSpace.map (ULift.{u} (Fin 1)) b) i i' (AffineSpace.map_over b) hi h h' C
  simpa only [sectionAlong, compAlong, lineCounit, endpointPull,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
    ProEtale.leftDerivedUpperStarCongr_rfl, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id, Functor.map_comp,
    ProEtale.leftDerivedUpperStarCongr_inv_app, Category.assoc] using H

private theorem endpoint_naturality {B B' : Scheme.{u}} (b : B' ⟶ B)
    (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (i' : B' ⟶ AffineSpace (ULift.{u} (Fin 1)) B')
    (hi : i' ≫ AffineSpace.map (ULift.{u} (Fin 1)) b = b ≫ i)
    {F G : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology (AffineSpace (ULift.{u} (Fin 1)) B))
        (ModuleCat.{u + 1} P.Coefficient))} (κ : F ≅ G) :
    let U := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor
    let V := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor
    let E := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor
    let E' := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i').leftDerivedFunctor
    endpointPull P b i i' hi F ≪≫ E'.mapIso (V.mapIso κ) =
      U.mapIso (E.mapIso κ) ≪≫ endpointPull P b i i' hi G := by
  apply Iso.ext
  let η := (ProEtale.leftDerivedUpperStarComp
      (ModuleCat.{u + 1} P.Coefficient) b i).symm ≪≫
    ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) hi.symm ≪≫
    ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) i'
      (AffineSpace.map (ULift.{u} (Fin 1)) b)
  exact (η.hom.naturality κ.hom).symm

private theorem transport_reading {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (A : C ⥤ D) (A' : C' ⥤ D') (U : C ⥤ C') (V : D ⥤ D')
    (E : D ⥤ C) (E' : D' ⥤ C') (ε : A ⋙ E ≅ 𝟭 C) (ε' : A' ⋙ E' ≅ 𝟭 C')
    (M : A ⋙ V ≅ U ⋙ A') {F : D} {X : C} {X' : C'}
    (κ : F ≅ A.obj X) (c : U.obj X ≅ X')
    (qF : U.obj (E.obj F) ≅ E'.obj (V.obj F))
    (qX : U.obj (E.obj (A.obj X)) ≅ E'.obj (V.obj (A.obj X)))
    (hq : qF ≪≫ E'.mapIso (V.mapIso κ) = U.mapIso (E.mapIso κ) ≪≫ qX)
    (hM : qX ≪≫ E'.mapIso (M.app X) ≪≫ ε'.app (U.obj X) =
      U.mapIso (ε.app X)) :
    qF ≪≫ E'.mapIso (V.mapIso κ ≪≫ M.app X ≪≫ A'.mapIso c) ≪≫ ε'.app X' =
      U.mapIso (E.mapIso κ ≪≫ ε.app X) ≪≫ c := by
  have hc : E'.mapIso (A'.mapIso c) ≪≫ ε'.app X' = ε'.app (U.obj X) ≪≫ c := by
    apply Iso.ext
    exact ε'.hom.naturality c.hom
  simp only [Functor.mapIso_trans, Iso.trans_assoc]
  rw [hc]
  have hm := congrArg (fun e ↦ U.mapIso (E.mapIso κ) ≪≫ e ≪≫ c) hM
  have hn := congrArg
    (fun e ↦ e ≪≫ E'.mapIso (M.app X) ≪≫ ε'.app (U.obj X) ≪≫ c) hq
  calc
    qF ≪≫ E'.mapIso (V.mapIso κ) ≪≫ E'.mapIso (M.app X) ≪≫ ε'.app (U.obj X) ≪≫ c =
        U.mapIso (E.mapIso κ) ≪≫ qX ≪≫ E'.mapIso (M.app X) ≪≫ ε'.app (U.obj X) ≪≫ c := by
      simpa only [Iso.trans_assoc] using hn
    _ = U.mapIso (E.mapIso κ) ≪≫ U.mapIso (ε.app X) ≪≫ c := by
      simpa only [Iso.trans_assoc] using hm

end Coherence

/-- A square between constant models which commutes at one commutes at zero.
This is a statement about arbitrary family objects and their trivializations; it
involves no DNC comparison, smooth section pair, or exceptional base-change map.
Source: latest blueprint, prop-pur-dnc-family-constancy, Base change; sk-thm-dnc,
Gluing, comparison of the two readings after restriction
(blueprint: lem-pur-constant-family-base-change).

Proof: let a and a' be the line projections and v the line map induced by b.
The equality v;a = a';b gives the canonical compositor b_line^* a^* = a'^* b^*.
Compose b_line^* kappa with that compositor and a'^* c. Precompose with T inverse,
obtaining a comparison from F' to a'^* C'. At one, the coherence of pullback
composition identifies its reading with b^* of the reading of kappa, followed by c.
The hypothesis says that this is the reading of kappa'. The stated detection
hypothesis, after cancelling the common section counit, makes the two comparisons
equal. Read this equality at zero. The same coherence of composition at zero gives
exactly the asserted equation. Coherence here follows by deriving the associativity
and unit equations for inverse image; equality constraints are transported along
the displayed equalities of scheme morphisms. No faithfulness of arbitrary derived
pullback, and no flatness or smoothness of b, is used. -/
theorem constant_family_base_change (P : PurityFiniteSetting.{u})
    {B B' : Scheme.{u}} (b : B' ⟶ B)
    (C : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient)))
    (C' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology B') (ModuleCat.{u + 1} P.Coefficient)))
    (F : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology (AffineSpace (ULift.{u} (Fin 1)) B))
        (ModuleCat.{u + 1} P.Coefficient)))
    (F' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology (AffineSpace (ULift.{u} (Fin 1)) B'))
        (ModuleCat.{u + 1} P.Coefficient))) :
    let A := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor
    let A' := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace (ULift.{u} (Fin 1)) B' ↘ B')).leftDerivedFunctor
    let Lb := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor
    let Lv := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor
    let E₁ := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor
    let E₁' := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B')).leftDerivedFunctor
    let E₀ := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor
    let E₀' := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B')).leftDerivedFunctor
    ∀ (κ : F ≅ A.obj C) (κ' : F' ≅ A'.obj C')
      (T : Lv.obj F ≅ F') (c : Lb.obj C ≅ C'),
      (∀ D (α β : F' ≅ A'.obj D), E₁'.mapIso α = E₁'.mapIso β → α = β) →
      (endpointPull P b _ _ (AffineSpace.oneSection_comp_map b) F ≪≫ E₁'.mapIso T ≪≫
        E₁'.mapIso κ' ≪≫
          (lineCounit P B' _ (AffineSpace.oneSection_comp_over _ B')).app C' =
        Lb.mapIso (E₁.mapIso κ ≪≫
          (lineCounit P B _ (AffineSpace.oneSection_comp_over _ B)).app C) ≪≫ c) →
      endpointPull P b _ _ (AffineSpace.zeroSection_comp_map b) F ≪≫ E₀'.mapIso T ≪≫
        E₀'.mapIso κ' ≪≫
          (lineCounit P B' _ (AffineSpace.zeroSection_comp_over _ B')).app C' =
        Lb.mapIso (E₀.mapIso κ ≪≫
          (lineCounit P B _ (AffineSpace.zeroSection_comp_over _ B)).app C) ≪≫ c := by
  dsimp only
  intro κ κ' T c hfaith h₁
  let a := (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)
  let a' := (AffineSpace (ULift.{u} (Fin 1)) B' ↘ B')
  let v := AffineSpace.map (ULift.{u} (Fin 1)) b
  let A := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor
  let A' := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a').leftDerivedFunctor
  let U := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor
  let V := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor
  let M : A ⋙ V ≅ U ⋙ A' :=
    (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) v a).symm ≪≫
      ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.map_over b) ≪≫
      ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) a' b
  let α : V.obj F ≅ A'.obj C' := V.mapIso κ ≪≫ M.app C ≪≫ A'.mapIso c
  have transport
      (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
      (i' : B' ⟶ AffineSpace (ULift.{u} (Fin 1)) B')
      (hi : i' ≫ v = b ≫ i) (h : i ≫ a = 𝟙 B) (h' : i' ≫ a' = 𝟙 B') :
      endpointPull P b i i' hi F ≪≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i').leftDerivedFunctor.mapIso α ≪≫
        (lineCounit P B' i' h').app C' =
      U.mapIso
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor.mapIso κ ≪≫
          (lineCounit P B i h).app C) ≪≫ c := by
    exact transport_reading A A' U V _ _ (lineCounit P B i h) (lineCounit P B' i' h')
      M κ c (endpointPull P b i i' hi F) (endpointPull P b i i' hi (A.obj C))
      (endpoint_naturality P b i i' hi κ)
      (line_projection_coherence P b i i' hi h h' C)
  have hmodel : α = T ≪≫ κ' := by
    let E := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B')).leftDerivedFunctor
    let q := endpointPull P b _ _ (AffineSpace.oneSection_comp_map b) F
    let ε := (lineCounit P B' _ (AffineSpace.oneSection_comp_over _ B')).app C'
    let κT := T.symm ≪≫ α
    have hα : α = T ≪≫ κT := by simp only [κT, Iso.self_symm_id_assoc]
    have he := (transport _ _ (AffineSpace.oneSection_comp_map b)
      (AffineSpace.oneSection_comp_over _ B)
      (AffineSpace.oneSection_comp_over _ B')).trans h₁.symm
    rw [hα, Functor.mapIso_trans] at he
    have he' := congrArg (fun e ↦ (E.mapIso T).symm ≪≫ q.symm ≪≫ e ≪≫ ε.symm) he
    have hκT : κT = κ' := by
      apply hfaith C'
      simpa only [E, q, ε, Iso.trans_assoc, Iso.symm_self_id_assoc,
        Iso.self_symm_id, Iso.trans_refl] using he'
    rw [hκT] at hα
    exact hα
  have hz := transport _ _ (AffineSpace.zeroSection_comp_map b)
    (AffineSpace.zeroSection_comp_over _ B) (AffineSpace.zeroSection_comp_over _ B')
  rw [hmodel, Functor.mapIso_trans] at hz
  simpa only [Iso.trans_assoc] using hz

end WeilConjectures.PurityFiniteSetting.SectionRestriction
