/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.EtaleGenericImmersionProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Parametrized
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # The evaluation-normalized internal-Hom formula for an immersion

Source: Stacks Project, Tags 08J9, 07A6 and 08FJ; blueprint
sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/lem-weil-stratum-ambient-hom
(blueprint: lem-sf-etale-generic-stratum-mate).

All categories below are ordinary unbounded derived categories of constant-coefficient
etale module sheaves. The internal Hom is the existing closed internal Hom `derivedHom`;
its tensor product is the existing K-flat derived tensor `derivedTensor`.
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace CategoryTheory

private noncomputable def transportParametrizedLeft
    {C D E : Type*} [Category C] [Category D] [Category E]
    {T T' : C ⥤ D ⥤ E} {H : Cᵒᵖ ⥤ E ⥤ D}
    (a : T ⊣₂ H) (e : T ≅ T') : T' ⊣₂ H :=
  ParametrizedAdjunction.mk' (fun P ↦ (a.adj P).ofNatIsoLeft (e.app P)) (by
    intro P Q f C M g
    simp only [Adjunction.homEquiv_ofNatIsoLeft_apply]
    rw [← Category.assoc]
    have h := NatTrans.congr_app (e.hom.naturality f) C
    change (T.map f).app C ≫ (e.app Q).hom.app C =
      (e.app P).hom.app C ≫ (T'.map f).app C at h
    rw [← h, Category.assoc]
    exact a.homEquiv_naturality_one f _)

private theorem flip_uncurry
    {C : Type*} [Category C] {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C}
    (a : T ⊣₂ H) (σ : T ≅ T.flip) (P M C₀ : C)
    (f : C₀ ⟶ (H.obj (op P)).obj M) :
    (((transportParametrizedLeft a
      ((flipFunctor _ _ _).mapIso σ.symm)).adj P).homEquiv _ _).symm f =
      (T.map f).app P ≫ (σ.hom.app ((H.obj (op P)).obj M)).app P ≫
        (a.adj P).counit.app M := by
  change (((a.adj P).ofNatIsoLeft
    (((flipFunctor C C C).mapIso σ.symm).app P)).homEquiv _ _).symm f = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  change (σ.hom.app C₀).app P ≫ ((a.adj P).homEquiv _ _).symm f = _
  rw [Adjunction.homEquiv_counit]
  have h := NatTrans.congr_app (σ.hom.naturality f) P
  change (T.map f).app P ≫ (σ.hom.app _).app P =
    (σ.hom.app _).app P ≫ (T.obj P).map f at h
  rw [← Category.assoc, ← h, Category.assoc]

private theorem conjugate_uncurry
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {C₀ : C} {M : D} (f : C₀ ⟶ R₁.obj M) :
    (a₂.homEquiv _ _).symm (f ≫ (conjugateEquiv a₁ a₂ α).app M) =
      α.app C₀ ≫ (a₁.homEquiv _ _).symm f := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit, ← α.naturality_assoc]

private theorem parametrized_conjugate_uncurry
    {C D E : Type*} [Category C] [Category D] [Category E]
    {T₁ T₂ : C ⥤ D ⥤ E} {H₁ H₂ : Cᵒᵖ ⥤ E ⥤ D}
    (a₁ : T₁ ⊣₂ H₁) (a₂ : T₂ ⊣₂ H₂) (π : T₂ ≅ T₁)
    (P : C) (M : E) (C₀ : D) (f : C₀ ⟶ (H₁.obj (op P)).obj M) :
    ((a₂.adj P).homEquiv C₀ M).symm
        (f ≫ ((a₁.conjugateIso a₂ π).hom.app (op P)).app M) =
      (π.hom.app P).app C₀ ≫ ((a₁.adj P).homEquiv C₀ M).symm f := by
  change ((a₂.adj P).homEquiv C₀ M).symm
    (f ≫ (conjugateEquiv (a₁.adj P) (a₂.adj P) (π.hom.app P)).app M) = _
  exact conjugate_uncurry (a₁.adj P) (a₂.adj P) (π.hom.app P) f

private theorem composite_conjugate_uncurry
    {C D : Type*} [Category C] [Category D]
    {TS : D ⥤ D ⥤ D} {HS : Dᵒᵖ ⥤ D ⥤ D}
    {TX : C ⥤ C ⥤ C} {HX : Cᵒᵖ ⥤ C ⥤ C}
    {F : D ⥤ C} {G : C ⥤ D} {L : C ⥤ D} {R : D ⥤ C}
    (tS : TS.flip ⊣₂ HS) (tX : TX.flip ⊣₂ HX) (a : L ⊣ R) (b : F ⊣ G)
    (π : F ⋙ TX.flip ≅ TS.flip ⋙ (Functor.whiskeringLeft _ _ _).obj L ⋙
      (Functor.whiskeringRight _ _ _).obj F)
    (P : D) (M C₀ : C) (f : C₀ ⟶ R.obj ((HS.obj (op P)).obj (G.obj M))) :
    ((tX.adj (F.obj P)).homEquiv C₀ M).symm
        (f ≫ (((tS.comp a b).conjugateIso (tX.precomp F) π).hom.app (op P)).app M) =
      (π.hom.app P).app C₀ ≫ F.map
        (((tS.adj P).homEquiv (L.obj C₀) (G.obj M)).symm
          ((a.homEquiv C₀ _).symm f)) ≫ b.counit.app M := by
  have h := parametrized_conjugate_uncurry (tS.comp a b) (tX.precomp F) π P M C₀ f
  simp only [ParametrizedAdjunction.precomp_adj, ParametrizedAdjunction.comp_adj,
    Adjunction.comp_homEquiv, Equiv.symm_trans, Equiv.trans_apply] at h
  change _ = (π.hom.app P).app C₀ ≫
    (b.homEquiv _ _).symm (((tS.adj P).homEquiv _ _).symm
      ((a.homEquiv _ _).symm f)) at h
  simpa only [Functor.comp_obj, Adjunction.homEquiv_counit, Category.assoc] using h

private noncomputable def projectionBifunctorIso
    {C D : Type*} [Category C] [Category D]
    (TX : C ⥤ C ⥤ C) (TS : D ⥤ D ⥤ D) (F : D ⥤ C) (L : C ⥤ D)
    (p : ∀ (C₀ : C) (P : D), (TX.obj C₀).obj (F.obj P) ⟶
      F.obj ((TS.obj (L.obj C₀)).obj P))
    [∀ C₀ P, IsIso (p C₀ P)]
    (hn : ∀ (C₀ C₁ : C) (P P' : D) (f : C₀ ⟶ C₁) (h : P ⟶ P'),
      ((TX.map f).app (F.obj P) ≫ (TX.obj C₁).map (F.map h)) ≫ p C₁ P' =
        p C₀ P ≫ F.map ((TS.map (L.map f)).app P ≫ (TS.obj (L.obj C₁)).map h)) :
    F ⋙ TX.flip ≅ TS.flip ⋙ (Functor.whiskeringLeft _ _ _).obj L ⋙
      (Functor.whiskeringRight _ _ _).obj F :=
  NatIso.ofComponents (fun P ↦ NatIso.ofComponents
    (fun C₀ ↦ asIso (p C₀ P)) (by
      intro C₀ C₁ f
      change (TX.map f).app (F.obj P) ≫ p C₁ P =
        p C₀ P ≫ F.map ((TS.map (L.map f)).app P)
      have h := hn C₀ C₁ P P f (𝟙 P)
      rw [F.map_id, (TX.obj C₁).map_id, (TS.obj (L.obj C₁)).map_id,
        Category.comp_id, Category.comp_id] at h
      exact h)) (by
    intro P P' h
    ext C₀
    change (TX.obj C₀).map (F.map h) ≫ p C₀ P' =
      p C₀ P ≫ F.map ((TS.obj (L.obj C₀)).map h)
    have hp := hn C₀ C₀ P P' (𝟙 C₀) h
    rw [L.map_id, TX.map_id, TS.map_id, NatTrans.id_app, NatTrans.id_app,
      Category.id_comp, Category.id_comp] at hp
    exact hp)

private theorem internalHomIsoOfProjection
    {C D : Type*} [Category C] [Category D]
    {TS : D ⥤ D ⥤ D} {HS : Dᵒᵖ ⥤ D ⥤ D}
    {TX : C ⥤ C ⥤ C} {HX : Cᵒᵖ ⥤ C ⥤ C}
    {F : D ⥤ C} {G : C ⥤ D} {L : C ⥤ D} {R : D ⥤ C}
    (tS : TS.flip ⊣₂ HS) (tX : TX.flip ⊣₂ HX) (a : L ⊣ R) (b : F ⊣ G)
    (π : F ⋙ TX.flip ≅ TS.flip ⋙ (Functor.whiskeringLeft _ _ _).obj L ⋙
      (Functor.whiskeringRight _ _ _).obj F) :
    ∃ θ : F.op.prod (𝟭 C) ⋙ Functor.uncurry.obj HX ≅
        (𝟭 Dᵒᵖ).prod G ⋙ Functor.uncurry.obj HS ⋙ R,
      ∀ (P : D) (M C₀ : C) (f : C₀ ⟶ R.obj ((HS.obj (op P)).obj (G.obj M))),
        ((tX.adj (F.obj P)).homEquiv C₀ M).symm (f ≫ θ.inv.app (op P, M)) =
          (π.hom.app P).app C₀ ≫ F.map
            (((tS.adj P).homEquiv (L.obj C₀) (G.obj M)).symm
              ((a.homEquiv C₀ _).symm f)) ≫ b.counit.app M := by
  let e := (tS.comp a b).conjugateIso (tX.precomp F) π
  let θ : F.op.prod (𝟭 C) ⋙ Functor.uncurry.obj HX ≅
      (𝟭 Dᵒᵖ).prod G ⋙ Functor.uncurry.obj HS ⋙ R :=
    NatIso.ofComponents (fun PM ↦ (e.symm.app PM.1).app PM.2) (by
      intro PM PM' g
      have h := (Functor.uncurry.mapIso e.symm).hom.naturality g
      change ((HX.map (F.op.map g.1)).app PM.2 ≫
        (HX.obj (F.op.obj PM'.1)).map g.2) ≫ (e.symm.hom.app PM'.1).app PM'.2 =
          (e.symm.hom.app PM.1).app PM.2 ≫
            (R.map ((HS.map g.1).app (G.obj PM.2)) ≫
              R.map ((HS.obj PM'.1).map (G.map g.2))) at h
      change ((HX.map (F.op.map g.1)).app PM.2 ≫
        (HX.obj (F.op.obj PM'.1)).map g.2) ≫ (e.symm.hom.app PM'.1).app PM'.2 =
          (e.symm.hom.app PM.1).app PM.2 ≫ R.map
            ((HS.map g.1).app (G.obj PM.2) ≫ (HS.obj PM'.1).map (G.map g.2))
      rw [R.map_comp]
      exact h)
  refine ⟨θ, ?_⟩
  intro P M C₀ f
  exact composite_conjugate_uncurry tS tX a b π P M C₀ f

private theorem internalHomIsoOfProjectionEvaluation
    {C D : Type*} [Category C] [Category D]
    {TS : D ⥤ D ⥤ D} {HS : Dᵒᵖ ⥤ D ⥤ D}
    {TX : C ⥤ C ⥤ C} {HX : Cᵒᵖ ⥤ C ⥤ C}
    {F : D ⥤ C} {G : C ⥤ D} {L : C ⥤ D} {R : D ⥤ C}
    (aS : TS ⊣₂ HS) (aX : TX ⊣₂ HX)
    (σS : TS ≅ TS.flip) (σX : TX ≅ TX.flip) (a : L ⊣ R) (b : F ⊣ G)
    (π : F ⋙ TX.flip ≅ TS.flip ⋙ (Functor.whiskeringLeft _ _ _).obj L ⋙
      (Functor.whiskeringRight _ _ _).obj F) :
    ∃ θ : F.op.prod (𝟭 C) ⋙ Functor.uncurry.obj HX ≅
        (𝟭 Dᵒᵖ).prod G ⋙ Functor.uncurry.obj HS ⋙ R,
      ∀ (P : D) (M C₀ : C) (f : C₀ ⟶ R.obj ((HS.obj (op P)).obj (G.obj M))),
        ((TX.map (f ≫ θ.inv.app (op P, M))).app (F.obj P) ≫
          (TX.obj ((HX.obj (op (F.obj P))).obj M)).map (𝟙 (F.obj P))) ≫
          ((σX.hom.app ((HX.obj (op (F.obj P))).obj M)).app (F.obj P) ≫
            (aX.adj (F.obj P)).counit.app M) =
        (π.hom.app P).app C₀ ≫ F.map
          ((TS.map ((a.homEquiv C₀ _).symm f)).app P ≫
            (TS.obj ((HS.obj (op P)).obj (G.obj M))).map (𝟙 P)) ≫ F.map
          ((σS.hom.app ((HS.obj (op P)).obj (G.obj M))).app P ≫
            (aS.adj P).counit.app (G.obj M)) ≫ b.counit.app M := by
  let tX := transportParametrizedLeft aX ((flipFunctor _ _ _).mapIso σX.symm)
  let tS := transportParametrizedLeft aS ((flipFunctor _ _ _).mapIso σS.symm)
  obtain ⟨θ, hθ⟩ := internalHomIsoOfProjection
    (TS := TS) (HS := HS) (TX := TX) (HX := HX) tS tX a b π
  refine ⟨θ, ?_⟩
  intro P M C₀ f
  have h := hθ P M C₀ f
  have hx := flip_uncurry aX σX (F.obj P) M C₀ (f ≫ θ.inv.app (op P, M))
  have hs := flip_uncurry aS σS P (G.obj M) (L.obj C₀)
    ((a.homEquiv C₀ ((HS.obj (op P)).obj (G.obj M))).symm f)
  change ((tX.adj (F.obj P)).homEquiv C₀ M).symm
    (f ≫ θ.inv.app (op P, M)) = _ at hx
  change ((tS.adj P).homEquiv (L.obj C₀) (G.obj M)).symm
    ((a.homEquiv C₀ ((HS.obj (op P)).obj (G.obj M))).symm f) = _ at hs
  have h' := hx.symm.trans h
  have h'' := congrArg (fun v ↦ (π.hom.app P).app C₀ ≫ F.map v ≫ b.counit.app M) hs
  simpa only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
    Functor.id_obj, Functor.op_obj, Functor.map_id, Category.comp_id,
    Category.id_comp, Functor.map_comp, Category.assoc] using h'.trans h''

private theorem internalHomIsoOfProjectionData
    {C D : Type*} [Category C] [Category D]
    {TS : D ⥤ D ⥤ D} {HS : Dᵒᵖ ⥤ D ⥤ D}
    {TX : C ⥤ C ⥤ C} {HX : Cᵒᵖ ⥤ C ⥤ C}
    {F : D ⥤ C} {G : C ⥤ D} {L : C ⥤ D} {R : D ⥤ C}
    (aS : TS ⊣₂ HS) (aX : TX ⊣₂ HX)
    (σS : TS ≅ TS.flip) (σX : TX ≅ TX.flip) (a : L ⊣ R) (b : F ⊣ G)
    (p : ∀ (C₀ : C) (P : D), (TX.obj C₀).obj (F.obj P) ⟶
      F.obj ((TS.obj (L.obj C₀)).obj P))
    [∀ C₀ P, IsIso (p C₀ P)]
    (hn : ∀ (C₀ C₁ : C) (P P' : D) (f : C₀ ⟶ C₁) (h : P ⟶ P'),
      ((TX.map f).app (F.obj P) ≫ (TX.obj C₁).map (F.map h)) ≫ p C₁ P' =
        p C₀ P ≫ F.map ((TS.map (L.map f)).app P ≫ (TS.obj (L.obj C₁)).map h)) :
    ∃ θ : F.op.prod (𝟭 C) ⋙ Functor.uncurry.obj HX ≅
        (𝟭 Dᵒᵖ).prod G ⋙ Functor.uncurry.obj HS ⋙ R,
      ∀ (P : D) (M C₀ : C) (f : C₀ ⟶ R.obj ((HS.obj (op P)).obj (G.obj M))),
        ((TX.map (f ≫ θ.inv.app (op P, M))).app (F.obj P) ≫
          (TX.obj ((HX.obj (op (F.obj P))).obj M)).map (𝟙 (F.obj P))) ≫
          ((σX.hom.app ((HX.obj (op (F.obj P))).obj M)).app (F.obj P) ≫
            (aX.adj (F.obj P)).counit.app M) =
        p C₀ P ≫ F.map
          ((TS.map ((a.homEquiv C₀ _).symm f)).app P ≫
            (TS.obj ((HS.obj (op P)).obj (G.obj M))).map (𝟙 P)) ≫ F.map
          ((σS.hom.app ((HS.obj (op P)).obj (G.obj M))).app P ≫
            (aS.adj P).counit.app (G.obj M)) ≫ b.counit.app M := by
  let π := projectionBifunctorIso TX TS F L p hn
  obtain ⟨θ, hθ⟩ := internalHomIsoOfProjectionEvaluation
    (TS := TS) (HS := HS) (TX := TX) (HX := HX) aS aX σS σX a b π
  exact ⟨θ, hθ⟩

private theorem internalHomIsoOfProjectionMaps
    {C D : Type*} [Category C] [Category D]
    {TS : D ⥤ D ⥤ D} {HS : Dᵒᵖ ⥤ D ⥤ D}
    {TX : C ⥤ C ⥤ C} {HX : Cᵒᵖ ⥤ C ⥤ C}
    {F : D ⥤ C} {G : C ⥤ D} {L : C ⥤ D} {R : D ⥤ C}
    (aS : TS ⊣₂ HS) (aX : TX ⊣₂ HX)
    (σS : TS ≅ TS.flip) (σX : TX ≅ TX.flip) (a : L ⊣ R) (b : F ⊣ G)
    (tensorX : ∀ {K K' M M' : C}, (K ⟶ K') → (M ⟶ M') →
      ((TX.obj K).obj M ⟶ (TX.obj K').obj M'))
    (tensorS : ∀ {K K' M M' : D}, (K ⟶ K') → (M ⟶ M') →
      ((TS.obj K).obj M ⟶ (TS.obj K').obj M'))
    (evX : ∀ P M : C, (TX.obj ((HX.obj (op P)).obj M)).obj P ⟶ M)
    (evS : ∀ P M : D, (TS.obj ((HS.obj (op P)).obj M)).obj P ⟶ M)
    (htX : ∀ {K K' M M' : C} (f : K ⟶ K') (g : M ⟶ M'),
      tensorX f g = (TX.map f).app M ≫ (TX.obj K').map g)
    (htS : ∀ {K K' M M' : D} (f : K ⟶ K') (g : M ⟶ M'),
      tensorS f g = (TS.map f).app M ≫ (TS.obj K').map g)
    (heX : ∀ P M, evX P M = (σX.hom.app ((HX.obj (op P)).obj M)).app P ≫
      (aX.adj P).counit.app M)
    (heS : ∀ P M, evS P M = (σS.hom.app ((HS.obj (op P)).obj M)).app P ≫
      (aS.adj P).counit.app M)
    (adjointTensor : ∀ (C₀ : C) (P : D) (M : D),
      (C₀ ⟶ R.obj M) → ((TS.obj (L.obj C₀)).obj P ⟶ (TS.obj M).obj P))
    (hadjointTensor : ∀ C₀ P M f,
      adjointTensor C₀ P M f = tensorS ((a.homEquiv C₀ M).symm f) (𝟙 P))
    (p : ∀ (C₀ : C) (P : D), (TX.obj C₀).obj (F.obj P) ⟶
      F.obj ((TS.obj (L.obj C₀)).obj P))
    [hiso : ∀ C₀ P, IsIso (p C₀ P)]
    (hn : ∀ (C₀ C₁ : C) (P P' : D) (f : C₀ ⟶ C₁) (h : P ⟶ P'),
      tensorX f (F.map h) ≫ p C₁ P' =
        p C₀ P ≫ F.map (tensorS (L.map f) h)) :
    ∃ θ : F.op.prod (𝟭 C) ⋙ Functor.uncurry.obj HX ≅
        (𝟭 Dᵒᵖ).prod G ⋙ Functor.uncurry.obj HS ⋙ R,
      ∀ (P : D) (M C₀ : C) (f : C₀ ⟶ R.obj ((HS.obj (op P)).obj (G.obj M))),
        tensorX (f ≫ θ.inv.app (op P, M)) (𝟙 (F.obj P)) ≫ evX (F.obj P) M =
          p C₀ P ≫ F.map (adjointTensor C₀ P _ f) ≫
            F.map (evS P (G.obj M)) ≫ b.counit.app M := by
  have hn' := hn
  simp only [htX, htS] at hn'
  obtain ⟨θ, hθ⟩ := internalHomIsoOfProjectionData aS aX σS σX a b p hn'
  refine ⟨θ, ?_⟩
  intro P M C₀ f
  simpa only [hadjointTensor, htX, htS, heX, heS, Functor.comp_obj, Functor.prod_obj,
    Functor.id_obj, Functor.op_obj, Functor.uncurry_obj_obj] using hθ P M C₀ f

end CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The exceptional inverse image `Ri^! j^*` for the specified closed-then-open factorization.
Source: blueprint lem-weil-stratum-ambient-hom and Stacks Tag 08FJ
(blueprint: lem-sf-etale-generic-stratum-mate). -/
noncomputable def immersionUpperShriek
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  D((j)^*[ModuleCat.{u + 1} A]) ⋙ (R((i)_*[ModuleCat.{u + 1} A])).rightAdjoint

/-- The composite closed/open adjunction, retaining its actual unit and counit.
Source: blueprint lem-weil-stratum-ambient-hom and Stacks Tags 07A6, 08FJ
(blueprint: lem-sf-etale-generic-stratum-mate). -/
noncomputable def immersionLowerUpperShriekAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    immersionLowerShriek A i j ⊣ immersionUpperShriek A i j :=
  (Adjunction.ofIsLeftAdjoint (R((i)_*[ModuleCat.{u + 1} A]))).comp
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)

/-- Right-ordered evaluation `RHom(P,M) ⊗ᴸ P ⟶ M`, obtained from the existing
left-tensor evaluation by the canonical signed symmetry. Source: Stacks Tag 08J9
(blueprint: lem-sf-etale-generic-stratum-mate). -/
noncomputable def immersionHomEvaluation
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj
      (((derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj M)).obj P ⟶ M :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app
      (((derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj M)).app P ≫
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) P).counit.app M

private theorem tensorHom_eq
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {K K' M M' : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (f : K ⟶ K') (g : M ⟶ M') :
    derivedTensorHom (X := T) (ModuleCat.{u + 1} A) f g =
      ((derivedTensor (ModuleCat.{u + 1} A) T).map f).app M ≫
        ((derivedTensor (ModuleCat.{u + 1} A) T).obj K').map g := by
  rfl

private theorem evaluation_eq
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    immersionHomEvaluation A T P M =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app
        (((derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj M)).app P ≫
        ((derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) T).adj P).counit.app M := by
  rfl

set_option Elab.async false in
/-- There is a natural internal-Hom isomorphism for an immersion, characterized by
its tensor transpose for every test object and every map into ordinary direct image.
Source: Stacks Tags 08J9, 07A6, 08FJ and blueprint lem-weil-stratum-ambient-hom
(blueprint: lem-sf-etale-generic-stratum-mate).

Proof plan:
1. The exact constant-coefficient inverse image and ordinary derived direct image form
an adjunction, computed on K-injectives. Use prop-weil-pbc-inverse-image-modules-exact,
prop-weil-pbc-kinjective-resolutions-exist, lem-weil-pbc-right-adjoint-preserves-kinjective,
lem-weil-pbc-kinjective-hom-derived, lem-weil-pbc-kinjective-total-derived and
lem-weil-pbc-termwise-adjunction-homotopy. The exact open adjunction descends termwise;
compose it with lem-exc-closed-ambient to obtain the specified shriek adjunction.
2. For each C, tensor-Hom adjunction (lem-sf-ringed-derived-closed-symmetric-monoidal),
the canonical immersion projection (lem-sf-etale-generic-immersion-projection), the shriek
adjunction, tensor-Hom adjunction on S, and inverse/direct-image adjunction give a
bijection Hom(C,RHom(Rs!P,M)) = Hom(C,Rs*RHom(P,Rs!M)), natural in C, P and M.
3. Yoneda yields the natural isomorphism. Tracing the inverse bijection sends a map u
to projection, Rs! of its adjoint tensor identity, Rs! evaluation, then the shriek counit.
4. The closed adjunction's counit is evaluation. Moving its left tensor factor to the
right uses exactly the signed symmetry in immersionHomEvaluation. This gives the
stated equality. No boundedness or constructibility enters any of these steps. -/
theorem immersionInternalHomIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    ∃ θ : (immersionLowerShriek A i j).op.prod
        (𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) X) ≅
      (𝟭 (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))ᵒᵖ).prod
        (immersionUpperShriek A i j) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) S) ⋙
          R((i ≫ j)_*[ModuleCat.{u + 1} A]),
      ∀ (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (M C : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (f : C ⟶ (R((i ≫ j)_*[ModuleCat.{u + 1} A])).obj
          (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
            ((immersionUpperShriek A i j).obj M))),
        derivedTensorHom (ModuleCat.{u + 1} A) (f ≫ θ.inv.app (op P, M))
            (𝟙 ((immersionLowerShriek A i j).obj P)) ≫
          immersionHomEvaluation A X ((immersionLowerShriek A i j).obj P) M =
        immersionProjectionMap A i j C P ≫
          (immersionLowerShriek A i j).map
            (derivedTensorHom (ModuleCat.{u + 1} A)
              (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
                (i ≫ j)).homEquiv C
                  (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
                    ((immersionUpperShriek A i j).obj M))).symm f) (𝟙 P)) ≫
          (immersionLowerShriek A i j).map
            (immersionHomEvaluation A S P ((immersionUpperShriek A i j).obj M)) ≫
          (immersionLowerUpperShriekAdjunction A i j).counit.app M := by
  have hπ := immersionProjectionFormula A i j
  exact internalHomIsoOfProjectionMaps
    (C := DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (D := DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (TS := derivedTensor (ModuleCat.{u + 1} A) S)
    (HS := derivedHom (ModuleCat.{u + 1} A) S)
    (TX := derivedTensor (ModuleCat.{u + 1} A) X)
    (HX := derivedHom (ModuleCat.{u + 1} A) X)
    (F := immersionLowerShriek A i j) (G := immersionUpperShriek A i j)
    (derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) S)
    (derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X)
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) S)
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) X)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (i ≫ j))
    (immersionLowerUpperShriekAdjunction A i j)
    (fun {K K' M M'} f g ↦ derivedTensorHom (X := X)
      (K := K) (K₁ := K') (M := M) (M₁ := M') (ModuleCat.{u + 1} A) f g)
    (fun {K K' M M'} f g ↦ derivedTensorHom (X := S)
      (K := K) (K₁ := K') (M := M) (M₁ := M') (ModuleCat.{u + 1} A) f g)
    (immersionHomEvaluation A X) (immersionHomEvaluation A S)
    (tensorHom_eq A X) (tensorHom_eq A S) (evaluation_eq A X) (evaluation_eq A S)
    (fun C₀ P M f ↦ derivedTensorHom (ModuleCat.{u + 1} A)
      (((derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) (i ≫ j)).homEquiv C₀ M).symm f) (𝟙 P))
    (by intros; rfl)
    (immersionProjectionMap A i j) (hiso := hπ.1) hπ.2.1

end AlgebraicGeometry.Etale
