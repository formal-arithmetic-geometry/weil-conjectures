/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q154 and C6
-/
module

public import Sheaf.SixFunctors.OpenScalarTensorData
import Sheaf.SixFunctors.OpenScalarTensorModels
import Sheaf.SixFunctors.OpenScalarProjectionCompatibility
import Sheaf.SixFunctors.OpenScalarCoefficientCoherence
import Sheaf.Paper.IntegralCompactSupportCoefficientData

/-! # Open scalar, tensor and coefficient normalization 

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6, 0D6D and 0GL1;
sites-modules.tex, Tag 0E8I
(blueprint: lem-fix-open-scalar-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor
variable (m : Models.{u})

private def transposeNatural
    {A B E : Type*} [Category A] [Category B] [Category E]
    {F : A ⥤ B} {G : B ⥤ A} (a : F ⊣ G) {P : E ⥤ A} {Q : E ⥤ B}
    (t : P ⟶ Q ⋙ G) : P ⋙ F ⟶ Q where
  app X := (a.homEquiv _ _).symm (t.app X)
  naturality _X _Y f := a.homEquiv_naturality_right_square _ _ _ _ (t.naturality f)

private def projectionInverse
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (q : TD ⋙ R ≅ (R.prod R) ⋙ TC) :
    ((𝟭 C).prod R) ⋙ TC ⋙ L ⟶ (L.prod (𝟭 D)) ⋙ TD := by
  let tau : ((𝟭 C).prod R) ⋙ TC ⟶ ((L.prod (𝟭 D)) ⋙ TD) ⋙ R :=
    { app X := TC.map (Prod.mkHom (a.unit.app X.1) (𝟙 _)) ≫
        q.inv.app (L.obj X.1, X.2)
      naturality X Y f := by
        have hn :
            Prod.mkHom f.1 (R.map f.2) ≫
                Prod.mkHom (a.unit.app Y.1) (𝟙 _) =
              Prod.mkHom (a.unit.app X.1) (𝟙 _) ≫
                (R.prod R).map (Prod.mkHom (L.map f.1) f.2) := by
          ext
          · exact a.unit.naturality f.1
          · simp
        dsimp only [Functor.prod_map, Functor.id_map, Functor.comp_map,
          Functor.prod_obj, Functor.comp_obj, Functor.id_obj]
        rw [← Category.assoc, ← TC.map_comp, hn, TC.map_comp,
          Category.assoc, Category.assoc]
        congr 1
        exact q.inv.naturality (Prod.mkHom (L.map f.1) f.2) }
  exact transposeNatural a tau

private def normalizedProjection (m : Models.{u}) (A : Type u) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : Projection m A j := by
  let v := projectionInverse (openAdj A j) (tensor m A U) (tensor m A X)
    (restrictionTensor m A j)
  have hi : ∀ Z, IsIso (v.app Z) := by
    intro Z
    exact PurCompactSupport.openProjectionInverse_isIso
      { ring := fun T ↦ proEtaleConstantRing T A
        pull := fun f ↦ proEtaleConstantRingComparison f A }
      j (tensorModel m A U) (tensorModel m A X) Z.1 Z.2
  letI : IsIso v := NatIso.isIso_of_isIso_app v
  exact { iso := (asIso v).symm
          inverse_adjunct := fun K Q ↦ ((openAdj A j).homEquiv _ _).apply_symm_apply _ }

set_option backward.defeqAttrib.useBackward true in
private theorem scalarOpenTranspose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) (K : C) :
    b.unit.app (SU.obj K) ≫ JB.map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      SU.map (a.unit.app K) ≫
        ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans.app (LA.obj K) := by
  apply (u.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((u.comp b).ofNatIsoRight q) (a.comp x) K
  change ((u.comp b).ofNatIsoRight q).unit.app K ≫
      (RX ⋙ JA).map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      (a.comp x).unit.app K at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc] at h
  have hn := q.hom.naturality
    (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [Functor.comp_obj] at h
  rw [← hn] at h
  have hm := unit_mateEquiv_symm x u (TwoSquare.mk _ _ _ _ q.inv) (LA.obj K)
  change JA.map (x.unit.app (LA.obj K)) ≫ q.inv.app (SX.obj (LA.obj K)) =
    u.unit.app (JA.obj (LA.obj K)) ≫ RU.map
      (((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans.app (LA.obj K)) at hm
  have hu := u.unit.naturality (a.unit.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hu
  rw [← reassoc_of% hu, ← hm]
  apply (cancel_mono (q.hom.app (SX.obj (LA.obj K)))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj,
    Adjunction.comp_unit_app] using h

private theorem transported_open_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX SX' : D ⥤ F} {SU SU' : C ⥤ E}
    (a : LA ⊣ JA) (b : LB ⊣ JB)
    (eX : SX' ≅ SX) (eU : SU' ≅ SU)
    (β : LA ⋙ SX ≅ SU ⋙ LB) (lam : SX ⋙ JB ≅ JA ⋙ SU)
    (h : ∀ K, b.homEquiv _ _ (β.inv.app K) =
      SU.map (a.unit.app K) ≫ lam.inv.app (LA.obj K)) (K : C) :
    b.homEquiv _ _
        ((Functor.isoWhiskerLeft LA eX ≪≫ β ≪≫
          Functor.isoWhiskerRight eU.symm LB).inv.app K) =
      SU'.map (a.unit.app K) ≫
        ((Functor.isoWhiskerRight eX JB ≪≫ lam ≪≫
          Functor.isoWhiskerLeft JA eU.symm).inv.app (LA.obj K)) := by
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Iso.symm_inv, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hu := b.unit.naturality (eU.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hu
  rw [← reassoc_of% hu]
  have hh := h K
  rw [Adjunction.homEquiv_unit] at hh
  rw [reassoc_of% hh]
  have hn := eU.hom.naturality (a.unit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn]

private theorem beta_inverse_aux {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : proEtaleDerivedCategory U A) :
    (openAdj B j).homEquiv _ _ ((beta m φ j).inv.app K) =
      (scalar m φ U).map ((openAdj A j).unit.app K) ≫
        (lambda m φ j).inv.app ((openExtension (A := A) j).obj K) := by
  apply transported_open_unit (openAdj A j) (openAdj B j)
    (scalarIso m φ X) (scalarIso m φ U) (openScalarIso φ j) (tensorPullbackIso φ j)
  intro L
  exact scalarOpenTranspose (openAdj A j) (openAdj B j)
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := U) φ))
    (rightSquare φ j) L

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem tensor_square
    {UA XA UB XB : Type*}
    [Category UA] [Category XA] [Category UB] [Category XB]
    {eA : UA ⥤ XA} {rA : XA ⥤ UA} {eB : UB ⥤ XB} {rB : XB ⥤ UB}
    (a : eA ⊣ rA) (b : eB ⊣ rB) (SX : XA ⥤ XB) (SU : UA ⥤ UB)
    (TA : XA × XA ⥤ XA) (TU : UA × UA ⥤ UA)
    (TB : XB × XB ⥤ XB) (TV : UB × UB ⥤ UB)
    (tX : TA ⋙ SX ≅ SX.prod SX ⋙ TB)
    (tU : TU ⋙ SU ≅ SU.prod SU ⋙ TV)
    (aA : TA ⋙ rA ≅ rA.prod rA ⋙ TU)
    (aB : TB ⋙ rB ≅ rB.prod rB ⋙ TV)
    (lam : SX ⋙ rB ≅ rA ⋙ SU) (bet : eA ⋙ SX ≅ SU ⋙ eB)
    (pA : eA.prod (𝟭 XA) ⋙ TA ≅ (𝟭 UA).prod rA ⋙ TU ⋙ eA)
    (pB : eB.prod (𝟭 XB) ⋙ TB ≅ (𝟭 UB).prod rB ⋙ TV ⋙ eB)
    (hb : ∀ K, b.homEquiv _ _ (bet.inv.app K) =
      SU.map (a.unit.app K) ≫ lam.inv.app (eA.obj K))
    (hpA : ∀ K Q, a.homEquiv _ _ (pA.inv.app (K, Q)) =
      TU.map (Prod.mkHom (a.unit.app K) (𝟙 _)) ≫ aA.inv.app (eA.obj K, Q))
    (hpB : ∀ K Q, b.homEquiv _ _ (pB.inv.app (K, Q)) =
      TV.map (Prod.mkHom (b.unit.app K) (𝟙 _)) ≫ aB.inv.app (eB.obj K, Q))
    (hm : ∀ F Q,
      TV.map (Prod.mkHom (lam.inv.app F) (lam.inv.app Q)) ≫
        aB.inv.app (SX.obj F, SX.obj Q) ≫ rB.map (tX.inv.app (F, Q)) =
      tU.inv.app (rA.obj F, rA.obj Q) ≫ SU.map (aA.inv.app (F, Q)) ≫
        lam.inv.app (TA.obj (F, Q))) (K : UA) (Q : XA) :
    SX.map (pA.hom.app (K, Q)) ≫ bet.hom.app (TU.obj (K, rA.obj Q)) ≫
        eB.map (tU.hom.app (K, rA.obj Q) ≫
          TV.map (Prod.mkHom (𝟙 _) (lam.inv.app Q))) =
      tX.hom.app (eA.obj K, Q) ≫ TB.map (Prod.mkHom (bet.hom.app K) (𝟙 _)) ≫
        pB.hom.app (SU.obj K, SX.obj Q) := by
  let L := SX.mapIso (pA.app (K, Q)) ≪≫ bet.app (TU.obj (K, rA.obj Q)) ≪≫
    eB.mapIso (tU.app (K, rA.obj Q) ≪≫
      TV.mapIso ((Iso.refl (SU.obj K)).prod (lam.symm.app Q)))
  let R := tX.app (eA.obj K, Q) ≪≫
    TB.mapIso ((bet.app K).prod (Iso.refl (SX.obj Q))) ≪≫
      pB.app (SU.obj K, SX.obj Q)
  have hi : L.inv = R.inv := by
    apply (b.homEquiv _ _).injective
    simp only [L, R, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      Iso.prod_inv, Iso.refl_inv, Iso.symm_inv, Category.assoc]
    change b.homEquiv _ _
        (eB.map (TV.map (Prod.mkHom (𝟙 _) (lam.hom.app Q)) ≫
          tU.inv.app (K, rA.obj Q)) ≫ bet.inv.app _ ≫
            SX.map (pA.inv.app (K, Q))) =
      b.homEquiv _ _ (pB.inv.app (SU.obj K, SX.obj Q) ≫
        TB.map (Prod.mkHom (bet.inv.app K) (𝟙 _)) ≫ tX.inv.app (eA.obj K, Q))
    simp only [Adjunction.homEquiv_unit, rB.map_comp]
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.prod_obj, Prod.fst, Prod.snd]
    have hu := b.unit.naturality
      (TV.map (Prod.mkHom (𝟙 (SU.obj K)) (lam.hom.app Q)) ≫
        tU.inv.app (K, rA.obj Q))
    dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hu
    rw [← reassoc_of% hu]
    have hbeta := hb (TU.obj (K, rA.obj Q))
    rw [Adjunction.homEquiv_unit] at hbeta
    rw [reassoc_of% hbeta]
    have hn := lam.inv.naturality (pA.inv.app (K, Q))
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hn
    rw [← hn, ← SU.map_comp_assoc]
    have hpa := hpA K Q
    rw [Adjunction.homEquiv_unit] at hpa
    dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hpa
    rw [hpa, SU.map_comp]
    simp only [Category.assoc]
    have ht := tU.inv.naturality (Prod.mkHom (a.unit.app K) (𝟙 (rA.obj Q)))
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_map, Functor.id_obj] at ht
    rw [← reassoc_of% ht, ← hm]
    rw [SU.map_id]
    simp only [← TV.map_comp_assoc]
    have hp : Prod.mkHom (𝟙 (SU.obj K)) (lam.hom.app Q) ≫
        Prod.mkHom (SU.map (a.unit.app K)) (𝟙 (SU.obj (rA.obj Q))) ≫
          Prod.mkHom (lam.inv.app (eA.obj K)) (lam.inv.app Q) =
        Prod.mkHom (SU.map (a.unit.app K) ≫ lam.inv.app (eA.obj K))
          (𝟙 (rB.obj (SX.obj Q))) := by
      ext <;> simp
    rw [hp]
    have hbk := hb K
    rw [Adjunction.homEquiv_unit] at hbk
    rw [← hbk]
    have hp' : Prod.mkHom (b.unit.app (SU.obj K) ≫ rB.map (bet.inv.app K))
        (𝟙 (rB.obj (SX.obj Q))) =
        Prod.mkHom (b.unit.app (SU.obj K)) (𝟙 _) ≫
          (rB.prod rB).map (Prod.mkHom (bet.inv.app K) (𝟙 (SX.obj Q))) := by
      ext <;> simp
    rw [hp', TV.map_comp, Category.assoc]
    have htB := aB.inv.naturality (Prod.mkHom (bet.inv.app K) (𝟙 (SX.obj Q)))
    dsimp only [Functor.comp_map, Functor.comp_obj] at htB
    rw [reassoc_of% htB]
    dsimp only [Functor.comp_obj, Prod.snd]
    have hpb := hpB (SU.obj K) (SX.obj Q)
    rw [Adjunction.homEquiv_unit] at hpb
    dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hpb
    rw [← reassoc_of% hpb]
  have he : L.symm = R.symm := Iso.ext hi
  have he' := congrArg (fun e ↦ e.inv) he
  simpa only [L, R, Iso.symm_inv, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc, Iso.prod_hom, Iso.symm_hom, Iso.refl_hom] using he'

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem coefficient_comp
    {UA XA UB XB UC XC : Type*}
    [Category UA] [Category XA] [Category UB] [Category XB] [Category UC] [Category XC]
    {eA : UA ⥤ XA} {rA : XA ⥤ UA} {eB : UB ⥤ XB} {rB : XB ⥤ UB}
    {eC : UC ⥤ XC} {rC : XC ⥤ UC}
    (a : eA ⊣ rA) (b : eB ⊣ rB) (c : eC ⊣ rC)
    (SX : XA ⥤ XB) (SU : UA ⥤ UB) (TX : XB ⥤ XC) (TU : UB ⥤ UC)
    (VX : XA ⥤ XC) (VU : UA ⥤ UC)
    (αX : SX ⋙ TX ≅ VX) (αU : SU ⋙ TU ≅ VU)
    (l : SX ⋙ rB ≅ rA ⋙ SU) (t : TX ⋙ rC ≅ rB ⋙ TU)
    (v : VX ⋙ rC ≅ rA ⋙ VU)
    (β : eA ⋙ SX ≅ SU ⋙ eB) (γ : eB ⋙ TX ≅ TU ⋙ eC)
    (δ : eA ⋙ VX ≅ VU ⋙ eC)
    (hb : ∀ K, b.homEquiv _ _ (β.inv.app K) =
      SU.map (a.unit.app K) ≫ l.inv.app (eA.obj K))
    (hc : ∀ K, c.homEquiv _ _ (γ.inv.app K) =
      TU.map (b.unit.app K) ≫ t.inv.app (eB.obj K))
    (hd : ∀ K, c.homEquiv _ _ (δ.inv.app K) =
      VU.map (a.unit.app K) ≫ v.inv.app (eA.obj K))
    (hl : ∀ Q,
      TU.map (l.inv.app Q) ≫ t.inv.app (SX.obj Q) ≫ rC.map (αX.hom.app Q) =
      αU.hom.app (rA.obj Q) ≫ v.inv.app Q) (K : UA) :
    TX.map (β.hom.app K) ≫ γ.hom.app (SU.obj K) ≫ eC.map (αU.hom.app K) =
      αX.hom.app (eA.obj K) ≫ δ.hom.app K := by
  let L := TX.mapIso (β.app K) ≪≫ γ.app (SU.obj K) ≪≫ eC.mapIso (αU.app K)
  let R := αX.app (eA.obj K) ≪≫ δ.app K
  have hi : L.inv = R.inv := by
    apply (cancel_mono (αX.hom.app (eA.obj K))).1
    simp only [L, R, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    apply (c.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, rC.map_comp]
    dsimp only [Functor.comp_obj]
    have hn := c.unit.naturality (αU.inv.app K)
    dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [← reassoc_of% hn]
    have hh := hc (SU.obj K)
    rw [Adjunction.homEquiv_unit] at hh
    rw [reassoc_of% hh]
    have hn' := t.inv.naturality (β.inv.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn'
    rw [← reassoc_of% hn', ← TU.map_comp_assoc]
    have hh' := hb K
    rw [Adjunction.homEquiv_unit] at hh'
    rw [hh', TU.map_comp]
    simp only [Category.assoc]
    rw [hl]
    have hα := αU.hom.naturality (a.unit.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hα
    rw [reassoc_of% hα]
    simp only [Iso.inv_hom_id_app_assoc]
    exact (hd K).symm
  have he : L.symm = R.symm := Iso.ext hi
  have hh := congrArg (fun z ↦ z.inv) he
  simpa only [L, R, Iso.symm_inv, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc] using hh

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem coefficient_id
    {U X : Type*} [Category U] [Category X]
    {e : U ⥤ X} {r : X ⥤ U} (a : e ⊣ r)
    (SX : X ⥤ X) (SU : U ⥤ U) (αX : SX ≅ 𝟭 X) (αU : SU ≅ 𝟭 U)
    (l : SX ⋙ r ≅ r ⋙ SU) (β : e ⋙ SX ≅ SU ⋙ e)
    (hb : ∀ K, a.homEquiv _ _ (β.inv.app K) =
      SU.map (a.unit.app K) ≫ l.inv.app (e.obj K))
    (hl : ∀ Q, l.inv.app Q ≫ r.map (αX.hom.app Q) = αU.hom.app (r.obj Q))
    (K : U) : β.hom.app K ≫ e.map (αU.hom.app K) = αX.hom.app (e.obj K) := by
  let L := β.app K ≪≫ e.mapIso (αU.app K)
  let R := αX.app (e.obj K)
  have hi : L.inv = R.inv := by
    apply (cancel_mono (αX.hom.app (e.obj K))).1
    simp only [L, R, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
      Category.assoc, Iso.inv_hom_id_app]
    apply (a.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, r.map_comp]
    dsimp only [Functor.id_obj]
    have hn := a.unit.naturality (αU.inv.app K)
    dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [← reassoc_of% hn]
    have hh := hb K
    rw [Adjunction.homEquiv_unit] at hh
    rw [reassoc_of% hh, hl]
    have hα := αU.hom.naturality (a.unit.app K)
    dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hα
    rw [hα]
    simp only [Iso.inv_hom_id_app_assoc, r.map_id]
    exact (Category.comp_id _).symm
  have he : L.symm = R.symm := Iso.ext hi
  have hh := congrArg (fun z ↦ z.inv) he
  simpa only [L, R, Iso.symm_inv, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using hh

/-- The canonical open scalar comparison is unit normalized, is the constant-B open
projection after restriction of scalars, respects coefficient composition and identities,
and preserves the open projection map with an arbitrary second tensor factor.
The existential objects are presentations of the already recorded universal derived
operations, not extra hypotheses on the rings, open immersion, or complexes.
Source: Stacks Project, sites-cohomology.tex, Tag 0GL1; sites-modules.tex, Tag 0E8I;
Tags 07A6, 08FJ and 0D6D
(blueprint: lem-fix-open-scalar-tensor-normalization).

Proof:
1. Choose the canonical scalar/tensor models and the normalized open monoidal
structures from `open_scalar_tensor_models`. Construct the inverse projection by
transposing the natural unit/tensorator map. The existing
`PurCompactSupport.openProjectionInverse_isIso` proves it invertible; its open
adjunct equation is the Hom equivalence inverse law. Obtain the scalar-restriction
interpretation from `open_scalar_projection_compatibility`.
2. Expand the composite units defining the common-right-adjoint beta, and use
scalar-unit naturality and the scalar mate equation. Transport by `scalarIso` to
obtain the open adjunct formula for inverse beta (`beta_inverse_aux`).
3. For coefficient composition compare inverse beta routes after the scalar
associator under the open Hom bijection. Substitute both beta adjunct formulas;
inverse-lambda naturality and its coefficient cocycle identify the middle factors.
Scalar-associator naturality at the open unit cancels its inverse. The same argument
with the scalar unitor and the inverse-lambda identity proves the identity case.
These are `coefficient_comp` and `coefficient_id`.
4. Compare inverse tensor-square routes under the open B Hom bijection. Substitute
the beta and projection adjuncts, use inverse-lambda naturality and inverse scalar
tensorator naturality, then apply its inverse tensor compatibility equation.
Lambda at Q cancels. Naturality of the B inverse restriction tensorator identifies
the second route with the same adjunct. Injectivity and inversion give the forward
square (`tensor_square`). All complexes are arbitrary and unbounded; no coefficient
flatness or quasi-compactness of the open is assumed. -/
theorem open_scalar_tensor_normalization :
    ∃ m : Models.{u}, ∃ c : Choices m, Nonempty (Normalization m c) := by
  obtain ⟨m, c, ⟨h⟩⟩ := open_scalar_tensor_models.{u}
  let p (A : Type u) [CommRing A] [Finite A] {U X : Scheme.{u}}
      (j : U ⟶ X) [IsOpenImmersion j] : Projection m A j := normalizedProjection m A j
  obtain ⟨pc⟩ := open_scalar_projection_compatibility m c p
  obtain ⟨coh⟩ := scalar_pullback_coefficient_coherence m
  refine ⟨m, c, ⟨{
    projection := p
    scalar_projection_isIso := h.scalar_projection_isIso
    restriction_open_isIso := pc.restriction_open_isIso
    beta_inverse := ?_
    restricted_beta := pc.restricted_beta
    coefficient_comp := ?_
    coefficient_id := ?_
    tensor_square := ?_ }⟩⟩
  · intro A B _ _ _ _ φ U X j _ K
    exact beta_inverse_aux m φ j K
  · intro A B C _ _ _ _ _ _ φ ψ U X j _ K
    exact coefficient_comp (openAdj A j) (openAdj B j) (openAdj C j)
      (scalar m φ X) (scalar m φ U) (scalar m ψ X) (scalar m ψ U)
      (scalar m (ψ.comp φ) X) (scalar m (ψ.comp φ) U)
      (scalarComp m φ ψ X) (scalarComp m φ ψ U)
      (lambda m φ j) (lambda m ψ j) (lambda m (ψ.comp φ) j)
      (beta m φ j) (beta m ψ j) (beta m (ψ.comp φ) j)
      (beta_inverse_aux m φ j) (beta_inverse_aux m ψ j)
      (beta_inverse_aux m (ψ.comp φ) j) (coh.composition φ ψ j) K
  · intro A _ _ U X j _ K
    exact coefficient_id (openAdj A j)
      (scalar m (RingHom.id A) X) (scalar m (RingHom.id A) U)
      (scalarId m A X) (scalarId m A U)
      (lambda m (RingHom.id A) j) (beta m (RingHom.id A) j)
      (beta_inverse_aux m (RingHom.id A) j) (coh.identity A j) K
  · intro A B _ _ _ _ φ U X j _ K Q
    exact tensor_square (openAdj A j) (openAdj B j)
      (scalar m φ X) (scalar m φ U)
      (tensor m A X) (tensor m A U) (tensor m B X) (tensor m B U)
      (c.scalarTensor φ X).iso (c.scalarTensor φ U).iso
      (restrictionTensor m A j) (restrictionTensor m B j)
      (lambda m φ j) (beta m φ j)
      (p A j).iso (p B j).iso
      (beta_inverse_aux m φ j)
      (p A j).inverse_adjunct (p B j).inverse_adjunct
      (h.lambda_tensor φ j) K Q

end AlgebraicGeometry.ProEtale.OpenScalarTensor
