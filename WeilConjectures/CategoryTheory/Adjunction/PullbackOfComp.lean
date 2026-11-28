/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Whiskering

/-!
# Pullbacks along adjunctions and transports of global sections

Abstract lemmas about composites of the shape
`B ⟶ B ⋙ R ⋙ L ≅ ... ⟶ L ⋙ A` built from the unit of an adjunction `L ⊣ R` and isomorphisms,
and about a transport `T : Γ ⟶ L ⋙ Γ` followed by the counit of an adjunction `L ⊣ R`
(`CategoryTheory.transportCounit`). They are the formal part of the comparison of the operators
of Frobenius correspondences with the global Frobenius operators on compactly supported
cohomology (`AlgebraicGeometry.Etale.correspondenceOperator_comp_eq_globalOperator`).
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- Naturality of `ι` along `f`, in a form avoiding a comparison of components of `ι` at
definitionally equal objects. -/
lemma comp_map_eq_of_naturality {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (ι : F ⟶ G) {P Q : C} (f : P ⟶ Q) {A : D} (e : A ⟶ F.obj P) (η : A ⟶ G.obj P)
    (hη : e ≫ ι.app P = η) (r : A ⟶ F.obj Q) (hr : e ≫ F.map f = r) :
    η ≫ G.map f = r ≫ ι.app Q := by
  rw [← hη, Category.assoc, ← ι.naturality, ← reassoc_of% hr]

/-- The components of a pullback of the shape of
`AlgebraicGeometry.Etale.lowerShriekPullbackOfComp`, for an abstract family of functors. -/
lemma pullbackOfComp_app {DX DY S : Type*} [Category DX] [Category DY] [Category S]
    {Lu : DY ⥤ DX} {Ru Su : DX ⥤ DY} {A : DY ⥤ S} {A' V : DX ⥤ S} (P : A ⟶ Lu ⋙ A')
    (adj : Lu ⊣ Ru) (ι : Su ≅ Ru) (c : V ≅ Su ⋙ A) (e : V ≅ A')
    (hP : P = (Functor.leftUnitor _).inv ≫ Functor.whiskerRight adj.unit A ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Lu (Functor.whiskerRight ι.inv A ≫ c.inv ≫ e.hom)) (K : DY) :
    P.app K = A.map (adj.unit.app K) ≫ A.map (ι.inv.app (Lu.obj K)) ≫ c.inv.app (Lu.obj K) ≫
      e.hom.app (Lu.obj K) := by
  subst hP
  simp

/-- For an adjunction `L ⊣ R` of endofunctors and a natural transformation `T : Γ ⟶ L ⋙ Γ`,
the composite `R ⋙ Γ ⟶ R ⋙ L ⋙ Γ ⟶ Γ` of `T` and the counit. -/
noncomputable def transportCounit {C E : Type*} [Category C] [Category E] {L R : C ⥤ C}
    (adj : L ⊣ R) (Γ : C ⥤ E) (T : Γ ⟶ L ⋙ Γ) : R ⋙ Γ ⟶ Γ :=
  Functor.whiskerLeft R T ≫ (Functor.associator R L Γ).inv ≫
    Functor.whiskerRight adj.counit Γ ≫ (Functor.leftUnitor Γ).hom

lemma transportCounit_app {C E : Type*} [Category C] [Category E] {L R : C ⥤ C}
    (adj : L ⊣ R) (Γ : C ⥤ E) (T : Γ ⟶ L ⋙ Γ) (B : C) :
    (transportCounit adj Γ T).app B = T.app (R.obj B) ≫ Γ.map (adj.counit.app B) := by
  simp [transportCounit]

/-- The transport along an endofunctor with a unit: for `L ⊣ R` and `T : Γ ⟶ L ⋙ Γ`,
`Γ(η_A ≫ R e) ≫ T_{RB} ≫ Γ(ε_B) = T_A ≫ Γ(e)`. -/
lemma map_unit_comp_transportCounit_app {C E : Type*} [Category C] [Category E] {L R : C ⥤ C}
    (adj : L ⊣ R) (Γ : C ⥤ E) (T : Γ ⟶ L ⋙ Γ) {A B : C} (e : L.obj A ⟶ B) :
    Γ.map (adj.unit.app A ≫ R.map e) ≫ (transportCounit adj Γ T).app B = T.app A ≫ Γ.map e := by
  rw [transportCounit_app, T.naturality_assoc]
  congr 1
  rw [Functor.comp_map, ← Γ.map_comp]
  congr 1
  simp

/-- The abstract form of
`AlgebraicGeometry.Etale.compactPullback_eq_whiskerRight_lowerShriekPullbackOfComp`: if the
adjunct of `Ex : Ra ⋙ Lh ⟶ Lg ⋙ Ra` under `Lh ⊣ Rp` is `pb` followed by `c : Rah ⟶ Ra ⋙ Rs`
and `ι : Rs ⟶ Rp`, then the transport `T` followed by `Γ(Ex)` is `Γ(pb)` followed by `Γ(c ≫ ι)`,
`T` and `Γ` of the counit. -/
lemma whiskerLeft_comp_whiskerRight_eq_whiskerRight_comp_whiskerLeft {DX Ds E : Type*}
    [Category DX]
    [Category Ds] [Category E] {Ra Rah : DX ⥤ Ds} {Lg : DX ⥤ DX} {Lh Rs Rp : Ds ⥤ Ds}
    (adj : Lh ⊣ Rp) (Γ : Ds ⥤ E) (T : Γ ⟶ Lh ⋙ Γ) (c : Rah ⟶ Ra ⋙ Rs) (ι : Rs ⟶ Rp)
    (Ex : Ra ⋙ Lh ⟶ Lg ⋙ Ra) (pb : Ra ⟶ Lg ⋙ Rah)
    (hF : ∀ K, adj.unit.app (Ra.obj K) ≫ Rp.map (Ex.app K) =
      pb.app K ≫ c.app (Lg.obj K) ≫ ι.app (Ra.obj (Lg.obj K))) :
    Functor.whiskerLeft Ra T ≫ (Functor.associator _ _ _).inv ≫ Functor.whiskerRight Ex Γ ≫
        (Functor.associator _ _ _).hom =
      Functor.whiskerRight pb Γ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft Lg (Functor.whiskerRight (c ≫ Functor.whiskerLeft Ra ι) Γ ≫
          (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Ra (transportCounit adj Γ T)) := by
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.id_comp, Category.comp_id,
    ← Γ.map_comp_assoc]
  rw [← hF]
  exact (map_unit_comp_transportCounit_app _ _ _ _).symm

/-- The abstract form of
`AlgebraicGeometry.Etale.correspondenceOperator_comp_eq_globalOperator`. -/
lemma map_app_comp_map_eq_app_comp_map {DX Ds E : Type*} [Category DX] [Category Ds]
    [Category E] {Ra Rah : DX ⥤ Ds} {Lg LF LΦ : DX ⥤ DX} (Γ : Ds ⥤ E) (pbg : Ra ⟶ Lg ⋙ Rah)
    (pbF : Rah ⟶ LF ⋙ Ra) (pbΦ : Ra ⟶ LΦ ⋙ Ra) (τ : LF ⟶ 𝟭 DX) (e : LΦ ≅ Lg ⋙ LF)
    (Q : Rah ⋙ Γ ⟶ Ra ⋙ Γ) (CP : Ra ⋙ Γ ⟶ Lg ⋙ Ra ⋙ Γ)
    (hΦ : ∀ K, pbΦ.app K = pbg.app K ≫ pbF.app (Lg.obj K) ≫ Ra.map (e.inv.app K))
    (hQ : Q =
      Functor.whiskerRight (pbF ≫ Functor.whiskerRight τ Ra ≫ (Functor.leftUnitor Ra).hom) Γ)
    (hCP : CP = Functor.whiskerRight pbg Γ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Lg Q) {K : DX} (v : Lg.obj K ⟶ K) :
    Γ.map (pbΦ.app K ≫ Ra.map (e.hom.app K ≫ τ.app (Lg.obj K) ≫ v)) =
      CP.app K ≫ (Ra ⋙ Γ).map v := by
  subst hQ hCP
  simp [hΦ]

/-- The components of the pullback of the shape of
`AlgebraicGeometry.Etale.lowerShriekPullbackOfComp` along a morphism whose pullback is
trivialized by `τ : Lu ≅ 𝟭`: followed by `A(τ)`, it is `B` of the inverse of the induced
trivialization `Su ≅ Ru ≅ 𝟭`, followed by `c⁻¹` and `e`. -/
lemma pullbackOfComp_app_comp_map_eq {DX S : Type*} [Category DX] [Category S]
    {Lu Ru Su : DX ⥤ DX} {A B V : DX ⥤ S} (P : B ⟶ Lu ⋙ A) (adj : Lu ⊣ Ru) (ι : Su ≅ Ru)
    (c : V ≅ Su ⋙ B) (e : V ≅ A) (τ : Lu ≅ 𝟭 DX)
    (hP : P = (Functor.leftUnitor _).inv ≫ Functor.whiskerRight adj.unit B ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Lu (Functor.whiskerRight ι.inv B ≫ c.inv ≫ e.hom)) (K : DX) :
    P.app K ≫ A.map (τ.hom.app K) =
      B.map ((ι ≪≫ adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft τ.symm)).inv.app K) ≫
        c.inv.app K ≫ e.hom.app K := by
  subst hP
  have hu := Adjunction.unit_rightAdjointUniq_hom_app adj (Adjunction.id.ofNatIsoLeft τ.symm) K
  have hn := (adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft τ.symm)).inv.naturality
    (τ.hom.app K)
  simp only [Functor.id_map] at hn
  have hu' : adj.unit.app K = τ.inv.app K ≫
      (adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft τ.symm)).inv.app (Lu.obj K) := by
    rw [← cancel_mono ((adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft τ.symm)).hom.app
      (Lu.obj K)), Category.assoc, Iso.inv_hom_id_app, hu]
    simp [Adjunction.ofNatIsoLeft]
  have key : adj.unit.app K ≫ Ru.map (τ.hom.app K) =
      (adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft τ.symm)).inv.app K := by
    rw [hu', Category.assoc, ← hn, Iso.inv_hom_id_app_assoc]
    rfl
  simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp, Iso.trans_inv,
    Category.assoc]
  rw [← e.hom.naturality, ← c.inv.naturality_assoc, Functor.comp_map, ← B.map_comp_assoc,
    ← B.map_comp_assoc, Category.assoc, ← ι.inv.naturality, reassoc_of% key, B.map_comp_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- The abstract form of the computation of the map
`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsTransport` for an inverse of the absolute
Frobenius of the base. -/
lemma eq_whiskerRight_of_transport {DX Ds E : Type*} [Category DX] [Category Ds] [Category E]
    {Ra Rah : DX ⥤ Ds} {LF : DX ⥤ DX} {Lw Rs Rp LF' L1 : Ds ⥤ Ds} (adj : Lw ⊣ Rp) (Γ : Ds ⥤ E)
    (T : Γ ⟶ Lw ⋙ Γ) (triv : LF' ≅ L1) (ε : L1 ≅ 𝟭 Ds) (κ : L1 ≅ LF' ⋙ Lw)
    (hT : ∀ N, T.app (LF'.obj N) ≫ Γ.map (κ.inv.app N) = Γ.map (triv.hom.app N))
    (c : Rah ⟶ Ra ⋙ Rs) (ι : Rs ⟶ Rp) (pb : Rah ⟶ LF ⋙ Ra) (τ : LF ⟶ 𝟭 DX)
    (hμ : ∀ M, c.app M ≫ ι.app (Ra.obj M) ≫ ε.inv.app (Rp.obj (Ra.obj M)) ≫
      κ.hom.app (Rp.obj (Ra.obj M)) ≫ Lw.map ((triv ≪≫ ε).hom.app (Rp.obj (Ra.obj M))) ≫
      adj.counit.app (Ra.obj M) = pb.app M ≫ Ra.map (τ.app M))
    (Q : Rah ⋙ Γ ⟶ Ra ⋙ Γ)
    (hQ : Q = Functor.whiskerRight (c ≫ Functor.whiskerLeft Ra ι) Γ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Ra (transportCounit adj Γ T)) :
    Q = Functor.whiskerRight (pb ≫ Functor.whiskerRight τ Ra ≫ (Functor.leftUnitor Ra).hom) Γ := by
  have hT' (N : Ds) : T.app N = Γ.map (ε.inv.app N ≫ κ.hom.app N ≫
      Lw.map ((triv ≪≫ ε).hom.app N)) := by
    have hn := T.naturality ((triv ≪≫ ε).hom.app N)
    simp only [Functor.comp_map, Functor.id_obj] at hn
    have h₀ : T.app (LF'.obj N) = Γ.map (triv.hom.app N) ≫ Γ.map (κ.hom.app N) := by
      rw [← hT, Category.assoc, ← Γ.map_comp, Iso.inv_hom_id_app]
      exact (Category.comp_id _).symm.trans (congrArg _ (Γ.map_id _).symm)
    rw [← cancel_epi (Γ.map ((triv ≪≫ ε).hom.app N)), hn, h₀, Iso.trans_hom, NatTrans.comp_app]
    simp only [Category.assoc, ← Γ.map_comp, Iso.hom_inv_id_app_assoc]
  subst hQ
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.leftUnitor_hom_app, Category.id_comp,
    transportCounit_app, hT', ← Γ.map_comp, Category.assoc]
  erw [Category.comp_id]
  exact congrArg Γ.map (hμ M)

/-- The final step of the computation of
`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsTransport`
for an inverse of the absolute Frobenius of the base, in a category. -/
lemma comp_eq_of_frobenius {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ : C}
    (cw : O₁ ⟶ O₂) (r : O₂ ⟶ O₃) (pbτ : O₁ ⟶ O₃) (ρX : O₄ ≅ O₁) (cFb : O₅ ≅ O₄) (ch : O₅ ≅ O₃)
    (ce : O₅ ≅ O₆) (cbs : O₆ ≅ O₇) (ρs : O₇ ≅ O₁) (Fcw : O₇ ⟶ O₈) (ρs' : O₈ ≅ O₂)
    (c₁₂ : O₆ ≅ O₃) (φ : O₉ ≅ O₃) (c₂ : O₁₀ ≅ O₉) (cws : O₁₀ ≅ O₈)
    (hA : pbτ = ρX.inv ≫ cFb.inv ≫ ch.hom)
    (hFr : cFb.hom ≫ ρX.hom = ce.hom ≫ cbs.hom ≫ ρs.hom)
    (hnat : ρs.hom ≫ cw = Fcw ≫ ρs'.hom)
    (hassoc : c₁₂.inv ≫ cbs.hom ≫ Fcw = φ.inv ≫ c₂.inv ≫ cws.hom)
    (hcore : c₂.inv ≫ cws.hom ≫ ρs'.hom ≫ r = φ.hom)
    (hcc : ce.hom ≫ c₁₂.hom = ch.hom) :
    cw ≫ r = pbτ := by
  have hFr' : ρX.inv ≫ cFb.inv = ρs.inv ≫ cbs.inv ≫ ce.inv := by
    have e : cFb ≪≫ ρX = ce ≪≫ cbs ≪≫ ρs := Iso.ext (by simpa using hFr)
    simpa using congrArg Iso.inv e
  rw [hA, reassoc_of% hFr', ← hcc, Iso.inv_hom_id_assoc, ← cancel_epi ρs.hom, Iso.hom_inv_id_assoc,
    ← cancel_epi cbs.hom, Iso.hom_inv_id_assoc, reassoc_of% hnat]
  have hassoc' : cbs.hom ≫ Fcw = c₁₂.hom ≫ φ.inv ≫ c₂.inv ≫ cws.hom := by
    rw [← hassoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hassoc', hcore, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory
