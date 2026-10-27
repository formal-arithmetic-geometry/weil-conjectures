/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import Sheaf.Paper.ScalarPullTensorCoefficientCoherence
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.SixFunctors.ExactLocalizationInverseMate

/-! The open projection square before the compactification pullback compositor.
(blueprint: lem-sf-open-projection-iso-coefficient-change).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction HasDerivedCategory.standard
  Functor.leftAdjoint proEtaleRingModulePullback proEtaleCanonicalTensorComparison


private theorem iso_tail
    {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (e : Y ≅ Z) :
    (f ≫ g ≫ e.hom) ≫ e.inv = f ≫ g := by
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem scalar_mate_of_adjuncts
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ A} {F' : C ⥤ D} {G' : D ⥤ C}
    {X : A ⥤ C} {Y : C ⥤ A} {U : B ⥤ D} {V : D ⥤ B}
    (r : F ⊣ G) (s : F' ⊣ G') (x : X ⊣ Y) (u : U ⊣ V)
    (q : F' ⋙ V ≅ Y ⋙ F) (d : G' ⋙ Y ≅ V ⋙ G)
    (h : ∀ (M : C) (N : D) (t : F'.obj M ⟶ N),
      r.homEquiv _ _ (q.inv.app M ≫ V.map t) =
        Y.map (s.homEquiv _ _ t) ≫ d.hom.app N) :
    ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans =
      (((r.comp u).ofNatIsoRight d.symm).leftAdjointUniq (x.comp s)).hom := by
  ext M
  apply (((r.comp u).ofNatIsoRight d.symm).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change r.homEquiv _ _ (u.homEquiv _ _
    (((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans.app M)) ≫
      d.inv.app _ = (x.comp s).unit.app M
  have hm := unit_mateEquiv_symm x u (TwoSquare.mk _ _ _ _ q.inv) M
  change F.map (x.unit.app M) ≫ q.inv.app (X.obj M) =
    u.unit.app (F.obj M) ≫ V.map
      (((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans.app M) at hm
  rw [Adjunction.homEquiv_unit u, ← hm, r.homEquiv_naturality_left]
  have hh := h (X.obj M) (F'.obj (X.obj M)) (𝟙 _)
  rw [V.map_id] at hh
  have hid := CategoryTheory.Category.comp_id (q.inv.app (X.obj M))
  dsimp only [Functor.comp_obj] at hid hh ⊢
  rw [hid] at hh
  have hs : s.homEquiv (X.obj M) (F'.obj (X.obj M)) (𝟙 _) =
      s.unit.app (X.obj M) := by
    rw [Adjunction.homEquiv_unit, G'.map_id]
    simpa only [Functor.comp_obj] using
      CategoryTheory.Category.comp_id (s.unit.app (X.obj M))
  rw [hs] at hh
  rw [hh]
  simpa only [Adjunction.comp_unit_app, Functor.comp_obj, Iso.app_hom, Iso.app_inv] using
    iso_tail (x.unit.app M) (Y.map (s.unit.app (X.obj M))) (d.app (F'.obj (X.obj M)))

private theorem scalarPull_is_mate
    {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) :
    ((mateEquiv (pbcDerivedScalarAdjunction (a.map V))
      (pbcDerivedScalarAdjunction (a.map U))).symm
      (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedPullback j
        (R.ring V) (S.ring V) (R.ring U) (S.ring U)
        (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)).inv)).natTrans =
      (scalarPull a j).hom := by
  exact scalar_mate_of_adjuncts
    (proEtaleRingDerivedAdjunction j (R.ring V) (R.ring U) (R.pull j))
    (proEtaleRingDerivedAdjunction j (S.ring V) (S.ring U) (S.pull j))
    (pbcDerivedScalarAdjunction (a.map V)) (pbcDerivedScalarAdjunction (a.map U))
    _ _ (proEtaleRingSheafChangeAdjunction j
      (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)).2.2

private theorem openRestriction_is_mate
    {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    (openRestriction a j).hom =
      ((mateEquiv (openDerivedAdjunction S j) (openDerivedAdjunction R j)).symm
        (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedPullback j
          (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)).hom)).natTrans := by
  let := proEtaleRingRestrictionPullbackInv_isIso j
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)
  let d := (asIso (proEtaleRingRestrictionPullbackInv j
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j))).symm
  have : IsIso ((mateEquiv (openAdjunction S j) (openAdjunction R j)).symm
      (TwoSquare.mk _ _ _ _ d.hom)).natTrans := openRestrictionMap_isIso a j
  exact (exact_localization_inverse_mate (openAdjunction S j)
    (openAdjunction R j) d).2.1.symm

private theorem openComparison_is_conjugate
    {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    openComparison a j =
      ((conjugateIsoEquiv
        ((pbcDerivedScalarAdjunction (a.map U)).comp (openDerivedAdjunction S j))
        ((openDerivedAdjunction R j).comp (pbcDerivedScalarAdjunction (a.map V)))).symm
          (proEtaleRingRestrictionDerivedPullback j
            (R.ring V) (S.ring V) (R.ring U) (S.ring U)
            (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j))).hom := by
  unfold openComparison
  rw [openRestriction_is_mate]
  exact congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm
      (pbcDerivedScalarAdjunction (a.map U)) (pbcDerivedScalarAdjunction (a.map V))
      (openDerivedAdjunction R j) (openDerivedAdjunction S j) _)

private theorem double_mate_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) (K : C) :
    b.homEquiv _ _
        (((conjugateIsoEquiv (u.comp b) (a.comp x)).symm q).inv.app K) =
      SU.map (a.unit.app K) ≫
        (((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans.app (LA.obj K)) := by
  have hm := unit_mateEquiv_symm a b
    ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)) K
  have hi := congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm a b u x (TwoSquare.mk _ _ _ _ q.inv))
  change ((mateEquiv a b).symm
    ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv))).natTrans =
      ((conjugateIsoEquiv (u.comp b) (a.comp x)).symm q).inv at hi
  change SU.map (a.unit.app K) ≫ _ = b.unit.app _ ≫ JB.map
    (((mateEquiv a b).symm
      ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv))).natTrans.app K) at hm
  rw [hi] at hm
  exact hm.symm

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
    (pA : ∀ K Q, TA.obj (eA.obj K, Q) ≅ eA.obj (TU.obj (K, rA.obj Q)))
    (pB : ∀ K Q, TB.obj (eB.obj K, Q) ≅ eB.obj (TV.obj (K, rB.obj Q)))
    (hb : ∀ K, b.homEquiv _ _ (bet.inv.app K) =
      SU.map (a.unit.app K) ≫ lam.inv.app (eA.obj K))
    (hpA : ∀ K Q, a.homEquiv _ _ ((pA K Q).inv) =
      TU.map (Prod.mkHom (a.unit.app K) (𝟙 _)) ≫ aA.inv.app (eA.obj K, Q))
    (hpB : ∀ K Q, b.homEquiv _ _ ((pB K Q).inv) =
      TV.map (Prod.mkHom (b.unit.app K) (𝟙 _)) ≫ aB.inv.app (eB.obj K, Q))
    (hm : ∀ F Q,
      TV.map (Prod.mkHom (lam.inv.app F) (lam.inv.app Q)) ≫
        aB.inv.app (SX.obj F, SX.obj Q) ≫ rB.map (tX.inv.app (F, Q)) =
      tU.inv.app (rA.obj F, rA.obj Q) ≫ SU.map (aA.inv.app (F, Q)) ≫
        lam.inv.app (TA.obj (F, Q))) (K : UA) (Q : XA) :
    SX.map ((pA K Q).hom) ≫ bet.hom.app (TU.obj (K, rA.obj Q)) ≫
        eB.map (tU.hom.app (K, rA.obj Q) ≫
          TV.map (Prod.mkHom (𝟙 _) (lam.inv.app Q))) =
      tX.hom.app (eA.obj K, Q) ≫ TB.map (Prod.mkHom (bet.hom.app K) (𝟙 _)) ≫
        (pB (SU.obj K) (SX.obj Q)).hom := by
  let L := SX.mapIso (pA K Q) ≪≫ bet.app (TU.obj (K, rA.obj Q)) ≪≫
    eB.mapIso (tU.app (K, rA.obj Q) ≪≫
      TV.mapIso ((Iso.refl (SU.obj K)).prod (lam.symm.app Q)))
  let R := tX.app (eA.obj K, Q) ≪≫
    TB.mapIso ((bet.app K).prod (Iso.refl (SX.obj Q))) ≪≫
      pB (SU.obj K) (SX.obj Q)
  have hi : L.inv = R.inv := by
    apply (b.homEquiv _ _).injective
    simp only [L, R, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      Iso.prod_inv, Iso.refl_inv, Iso.symm_inv, Category.assoc]
    change b.homEquiv _ _
        (eB.map (TV.map (Prod.mkHom (𝟙 _) (lam.hom.app Q)) ≫
          tU.inv.app (K, rA.obj Q)) ≫ bet.inv.app _ ≫
            SX.map ((pA K Q).inv)) =
      b.homEquiv _ _ ((pB (SU.obj K) (SX.obj Q)).inv ≫
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
    have hn := lam.inv.naturality ((pA K Q).inv)
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


/-- Coefficient change commutes with the open projection isomorphism itself.

Source: Stacks Project, Tags 0E8I and 07A6; this is the open-unit tensor step
of the proof of `lem-sf-open-projection-factor-coefficient-change`.
The pullback compositor of a compactification is omitted, so this statement is
strictly the open factor of the target theorem.
(blueprint: lem-sf-open-projection-iso-coefficient-change).
-/
theorem openProjectionIso_coefficient_change
    {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (aU : ProEtaleTensorModel U (R.ring U))
    (aV : ProEtaleTensorModel V (R.ring V))
    (bU : ProEtaleTensorModel U (S.ring U))
    (bV : ProEtaleTensorModel V (S.ring V))
    (M : DerivedCategory (pbcModules U (R.ring U)))
    (Q : DerivedCategory (pbcModules V (R.ring V))) :
    (pbcDerivedExtend (a.map V)).map
        (openProjectionIso R j aU aV M Q).hom ≫
      (openComparison a j).app (aU.tensor.obj (M, (pull R j).obj Q)) ≫
      (openExtension S j).mapDerivedCategory.map
        ((scalarTensor (a.map U) aU bU).hom.app (M, (pull R j).obj Q) ≫
          bU.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a j).hom.app Q))) =
    (scalarTensor (a.map V) aV bV).hom.app
        ((openExtension R j).mapDerivedCategory.obj M, Q) ≫
      bV.tensor.map (Prod.mkHom ((openComparison a j).app M) (𝟙 _)) ≫
      (openProjectionIso S j
        bU bV ((pbcDerivedExtend (a.map U)).obj M)
        ((pbcDerivedExtend (a.map V)).obj Q)).hom := by
  let JR := (openExtension R j).mapDerivedCategory
  let PR := pull R j
  let PS := pull S j
  let CV := pbcDerivedExtend (a.map V)
  let CU := pbcDerivedExtend (a.map U)
  let tV := scalarTensor (a.map V) aV bV
  let tU := scalarTensor (a.map U) aU bU
  let rR := proEtaleCanonicalTensorComparison j
    (R.ring V) (R.ring U) (R.pull j) aV aU
  let rS := proEtaleCanonicalTensorComparison j
    (S.ring V) (S.ring U) (S.pull j) bV bU
  let q := proEtaleRingRestrictionDerivedPullback j
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)
  let beta := (conjugateIsoEquiv
    ((pbcDerivedScalarAdjunction (a.map U)).comp (openDerivedAdjunction S j))
    ((openDerivedAdjunction R j).comp (pbcDerivedScalarAdjunction (a.map V)))).symm q
  have hb (K : DerivedCategory (pbcModules U (R.ring U))) :
      (openDerivedAdjunction S j).homEquiv _ _ (beta.inv.app K) =
        CU.map ((openDerivedAdjunction R j).unit.app K) ≫
          (scalarPull a j).hom.app (JR.obj K) := by
    have h := double_mate_unit (openDerivedAdjunction R j) (openDerivedAdjunction S j)
      (pbcDerivedScalarAdjunction (a.map V)) (pbcDerivedScalarAdjunction (a.map U)) q K
    rw [scalarPull_is_mate] at h
    exact h
  have hm (P Q : DerivedCategory (pbcModules V (R.ring V))) :
      bU.tensor.map (Prod.mkHom ((scalarPull a j).hom.app P)
        ((scalarPull a j).hom.app Q)) ≫
        rS.inv.app (CV.obj P, CV.obj Q) ≫ PS.map (tV.inv.app (P, Q)) =
      tU.inv.app (PR.obj P, PR.obj Q) ≫ CU.map (rR.inv.app (P, Q)) ≫
        (scalarPull a j).hom.app (aV.tensor.obj (P, Q)) := by
    let L := (scalarPull a j).symm.app (aV.tensor.obj (P, Q)) ≪≫
      CU.mapIso (rR.app (P, Q)) ≪≫ tU.app (PR.obj P, PR.obj Q)
    let T := PS.mapIso (tV.app (P, Q)) ≪≫ rS.app (CV.obj P, CV.obj Q) ≪≫
      bU.tensor.mapIso (((scalarPull a j).symm.app P).prod
        ((scalarPull a j).symm.app Q))
    have he : L.hom = T.hom := scalarPull_tensor_coefficient_coherence a j aU aV bU bV P Q
    have hi := congrArg Iso.inv (Iso.ext he)
    simpa only [L, T, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      Iso.prod_inv, Iso.symm_inv, Category.assoc] using hi.symm
  simp only [openComparison_is_conjugate]
  exact tensor_square (openDerivedAdjunction R j) (openDerivedAdjunction S j) CV CU
    aV.tensor aU.tensor bV.tensor bU.tensor tV tU rR rS (scalarPull a j).symm beta
    (openProjectionIso R j aU aV) (openProjectionIso S j bU bV) hb
    (fun K Q ↦ ((openDerivedAdjunction R j).homEquiv _ _).apply_symm_apply _)
    (fun K Q ↦ ((openDerivedAdjunction S j).homEquiv _ _).apply_symm_apply _) hm M Q

end WeilConjectures.PurCompactSupport
