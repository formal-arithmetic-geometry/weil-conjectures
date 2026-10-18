/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ProperPushforwardKernel
public import WeilConjectures.TraceFormula.TraceClassAdditivity

/-!

# The Lefschetz–Verdier formula

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {P X C : Type*} [Category* P] [Category* X] [Category* C]

/-- The unit of a composite adjunction through the conjugate of a composition isomorphism
`σ : L_g ≅ L_f ⋙ L_c`: with `λ : R_c ⋙ R_f ≅ R_g` the conjugate of `σ`,
`R_f η_c ≫ λ = η_g ≫ R_g (σ ≫ L_c ε_f)`. -/
lemma map_unit_comp_conjugateIsoEquiv_inv_app {Lf : P ⥤ X} {Rf : X ⥤ P} {Lc : X ⥤ C}
    {Rc : C ⥤ X} {Lg : P ⥤ C} {Rg : C ⥤ P} (adjf : Lf ⊣ Rf) (adjc : Lc ⊣ Rc) (adjg : Lg ⊣ Rg)
    (σ : Lg ≅ Lf ⋙ Lc) (K : X) :
    Rf.map (adjc.unit.app K) ≫
        (conjugateIsoEquiv adjg (adjf.comp adjc) σ.symm).inv.app (Lc.obj K) =
      adjg.unit.app (Rf.obj K) ≫ Rg.map (σ.hom.app (Rf.obj K) ≫ Lc.map (adjf.counit.app K)) := by
  simp only [conjugateIsoEquiv_apply_inv, Iso.symm_inv, conjugateEquiv_apply_app,
    Adjunction.comp_counit_app, Functor.comp_obj]
  have h1 := adjg.unit.naturality (Rf.map (adjc.unit.app K))
  have h2 := σ.hom.naturality (Rf.map (adjc.unit.app K))
  have h3 := adjf.counit.naturality (adjc.unit.app K)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h1 h2 h3
  rw [reassoc_of% h1, ← Rg.map_comp, ← Rg.map_comp]
  congr 2
  rw [reassoc_of% h2, ← Lc.map_comp_assoc, h3, Lc.map_comp, Category.assoc,
    Adjunction.left_triangle_components, Category.comp_id]

/-- For an adjunction `L ⊣ R` with `Λ : L ≅ 𝟭`, the unit followed by the conjugate
`R ≅ 𝟭` of `Λ` is `Λ⁻¹`. -/
@[reassoc]
lemma unit_map_comp_conjugateIsoEquiv_hom_app {L R : P ⥤ P} (adj : L ⊣ R) (Λ : L ≅ 𝟭 P)
    {Z Y : P} (φ : L.obj Z ⟶ Y) :
    adj.unit.app Z ≫ R.map φ ≫ (conjugateIsoEquiv adj Adjunction.id Λ.symm).hom.app Y =
      Λ.inv.app Z ≫ φ := by
  simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom, conjugateEquiv_apply_app]
  have h1 := Λ.inv.naturality (R.map φ)
  have h2 := Λ.inv.naturality (adj.unit.app Z)
  simp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at h1 h2
  simp only [Adjunction.id, Functor.id_map, Functor.id_obj, Category.id_comp, NatTrans.id_app]
  rw [reassoc_of% h1, reassoc_of% h2, Adjunction.counit_naturality,
    Adjunction.left_triangle_components_assoc]


/-- Abstract form of the ordinary half of the global operator: the unit of `L_c ⊣ R_c` read
through the lower shriek functors `S_f, S_c, S_g` (`ι : S ≅ R`) and the composition isomorphism
`κ : S_g ≅ S_c ⋙ S_f` is the unit of `L_g ⊣ R_g` followed by the counit of `L_f ⊣ R_f`, up to
`Θ : L_1 ≅ 𝟭`. -/
lemma map_unit_comp_inv_eq_aux {Lf : P ⥤ X} {Rf Sf : X ⥤ P} {Lc : X ⥤ C} {Rc Sc : C ⥤ X}
    {Lg : P ⥤ C} {Rg Sg : C ⥤ P} {L1 : P ⥤ P} (adjf : Lf ⊣ Rf) (adjc : Lc ⊣ Rc)
    (adjg : Lg ⊣ Rg) (σ : Lg ≅ Lf ⋙ Lc) (ιf : Sf ≅ Rf) (ιc : Sc ≅ Rc) (ιg : Sg ≅ Rg)
    (κ : Sg ≅ Sc ⋙ Sf) (lam : Rc ⋙ Rf ≅ Rg)
    (hκ : ∀ M, κ.hom.app M ≫ ιf.hom.app (Sc.obj M) ≫ Rf.map (ιc.hom.app M) =
      ιg.hom.app M ≫ lam.inv.app M)
    (hlam : ∀ K, Rf.map (adjc.unit.app K) ≫ lam.hom.app (Lc.obj K) =
      adjg.unit.app (Rf.obj K) ≫ Rg.map (σ.hom.app (Rf.obj K) ≫ Lc.map (adjf.counit.app K)))
    (Θ : L1 ≅ 𝟭 P) (K : X) :
    Sf.map (adjc.unit.app K) ≫ Sf.map (ιc.inv.app (Lc.obj K)) ≫ κ.inv.app (Lc.obj K) =
      ιf.hom.app K ≫ Θ.inv.app (Rf.obj K) ≫ adjg.unit.app (L1.obj (Rf.obj K)) ≫
        Rg.map (Lg.map (Θ.hom.app (Rf.obj K)) ≫ σ.hom.app (Rf.obj K) ≫
          Lc.map (adjf.counit.app K)) ≫ ιg.inv.app (Lc.obj K) := by
  have e (M : C) : κ.inv.app M =
      ιf.hom.app (Sc.obj M) ≫ Rf.map (ιc.hom.app M) ≫ lam.hom.app M ≫ ιg.inv.app M := by
    rw [← cancel_epi (κ.hom.app M), Iso.hom_inv_id_app, reassoc_of% (hκ M)]
    simp
  have hu := adjg.unit.naturality (Θ.hom.app (Rf.obj K))
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hu
  rw [e, ← Sf.map_comp_assoc, ιf.hom.naturality_assoc, ← Rf.map_comp_assoc, Category.assoc]
  simp only [Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj, Functor.id_obj]
  rw [reassoc_of% (hlam K)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hu, Iso.inv_hom_id_app_assoc]

/-- A component of the mate of a two-square. -/
lemma mateEquiv_app_eq {D E : Type*} [Category* D] [Category* E] {G : C ⥤ D} {H : X ⥤ E}
    {L₁ : C ⥤ X} {R₁ : X ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (d : X) :
    (mateEquiv adj₁ adj₂ α).app d = adj₂.unit.app (G.obj (R₁.obj d)) ≫
      R₂.map (α.app (R₁.obj d) ≫ H.map (adj₁.counit.app d)) := by
  simp [mateEquiv_apply]

/-- Abstract form of the exceptional half of the global operator: the mate of the composition
isomorphism `Ξ = S_1 ι_g⁻¹ ≫ κ₁⁻¹ ≫ e ≫ κ₂ ≫ ι_f`, read through `R_1 ≅ 𝟭` and the
identifications `ι`, is the composition isomorphism followed by the counit. -/
lemma mateEquiv_app_comp_eq_aux {Sg Rg Sg' Sg'' : C ⥤ P} {S1 U1 : P ⥤ P} {Sc1 : C ⥤ X}
    {Uc1 : X ⥤ C} {Sf Rf : X ⥤ P} (adj1 : S1 ⊣ U1) (adjc1 : Sc1 ⊣ Uc1) (Λ : S1 ≅ 𝟭 P)
    (ιg : Sg ≅ Rg) (ιf : Sf ≅ Rf) (κ1 : Sg' ≅ Sg ⋙ S1) (θ1 : Sg ⟶ Sg')
    (hκ1 : ∀ M, κ1.inv.app M = Λ.hom.app (Sg.obj M) ≫ θ1.app M)
    (eqIso : Sg' ≅ Sg'') (κ2 : Sg'' ≅ Sc1 ⋙ Sf) (K : X) :
    ιg.hom.app (Uc1.obj K) ≫
        (mateEquiv adjc1 adj1 (Functor.isoWhiskerRight ιg.symm S1 ≪≫ κ1.symm ≪≫ eqIso ≪≫ κ2 ≪≫
          Functor.isoWhiskerLeft Sc1 ιf).hom).app K ≫
        (conjugateIsoEquiv adj1 Adjunction.id Λ.symm).hom.app (Rf.obj K) ≫ ιf.inv.app K =
      θ1.app (Uc1.obj K) ≫ eqIso.hom.app _ ≫ κ2.hom.app _ ≫ Sf.map (adjc1.counit.app K) := by
  rw [mateEquiv_app_eq]
  simp only [Category.assoc]
  have hn := Λ.inv.naturality (ιg.inv.app (Uc1.obj K))
  simp only [Functor.id_map, Functor.id_obj] at hn
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc]
  erw [unit_map_comp_conjugateIsoEquiv_hom_app_assoc]
  have hf := ιf.inv.naturality (adjc1.counit.app K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hf
  simp only [Category.assoc, hκ1]
  rw [← reassoc_of% hn, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc, hf,
    Iso.hom_inv_id_app_assoc]
end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Coherence

variable {C X Y : Over (Spec (.of k))} [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
  [IsSeparated C.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

variable (ℓ) in
/-- The right unit law for the composition isomorphisms of the derived pullbacks, inverse form. -/
@[reassoc]
lemma boundedConstructibleUpperStarComp_id_right_inv_app (f : X ⟶ Y)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f (𝟙 Y)).inv.app K ≫
        eqToHom (by rw [Category.comp_id]; rfl) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).hom.app K) := by
  rw [← cancel_epi ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f
    (𝟙 Y)).hom.app K), Iso.hom_inv_id_app_assoc, boundedConstructibleUpperStarComp_id_right_app]

variable (ℓ) in
/-- The right unit law for the composition isomorphisms of the lower shriek, inverse form. -/
lemma boundedConstructibleLowerShriekComp_padicAlgCl_id_right_inv_app (f : X ⟶ Y)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 Y)).inv.app K =
      (boundedConstructibleLowerShriekId ℓ Y).hom.app _ ≫
        eqToHom (by rw [Category.comp_id]; rfl) := by
  rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 Y)).hom.app K),
    Iso.hom_inv_id_app, boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app,
    ← Category.assoc, boundedConstructibleLowerShriekComp_padicAlgCl_id_right ℓ f K,
    eqToHom_trans, eqToHom_refl]

variable (ℓ) in
/-- The ordinary half of the global operator (blueprint `thm-trf-fixed-point-localization`,
proof): for `c₂ ≫ f = g`, the unit of `Lc₂^* ⊣ Rc₂_*` read on `Rf_!` is the ordinary half `γ` of
the coefficient pushforward along `(f, g)`. -/
lemma lowerShriek_map_unit_eq_pushforwardCoeffUnit_aux (c₂ : C ⟶ X) (f : X ⟶ Y) (g : C ⟶ Y)
    [IsProper c₂.left] [IsProper f.left] [IsProper g.left] (hg : c₂ ≫ f = g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ c₂).unit.app K) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ c₂).inv.app _) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c₂ f).inv.app _ ≫
      eqToHom (by rw [hg]; rfl) =
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K ≫
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).inv.app _ ≫
      ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app _ ≫
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g (𝟙 Y)).inv.app
              _ ≫
            eqToHom (by rw [Category.comp_id, hg]; rfl) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ c₂ f).hom.app
              _ ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).map
              ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).counit.app K))) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app _ := by
  subst hg
  rw [boundedConstructibleUpperStarComp_id_right_inv_app_assoc]
  simp only [eqToHom_refl, Category.comp_id, Category.assoc]
  exact CategoryTheory.map_unit_comp_inv_eq_aux
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ c₂)
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (c₂ ≫ f))
    (boundedConstructibleUpperStarComp _ ℓ c₂ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ c₂)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (c₂ ≫ f))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c₂ f)
    (boundedConstructibleLowerStarComp _ ℓ c₂ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ c₂ f)
    (CategoryTheory.map_unit_comp_conjugateIsoEquiv_inv_app _ _ _ _)
    (boundedConstructibleUpperStarId _ ℓ Y) K

end Coherence

end AlgebraicGeometry.ProEtale.CondensedRing
