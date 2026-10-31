/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.ProperCoordinates.IntegralProperProjectionCoefficientData

import WeilConjectures.SmoothPurity.IntegralSystemRealization.SystemPullbackCompositorEvaluation
import all WeilConjectures.SixFunctors.IntegralSystemRealization.SystemPushIdentityPullUnit
import all WeilConjectures.AlgebraicGeometry.AmbientProperOpen.OrdinaryAmbientAlphaUnits
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange

/-! # Finite evaluation of the identity open extension

Source: fix-prop-projection-formula.proof.md, proper-coincidence normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
universe u
attribute [local irreducible] sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
  sfIntrinsicOpenAdjunction Adjunction.leftAdjointIdIso

/-- An identity comparison commutes with applying its own functor. -/
private theorem identity_naturality
    {A : Type*} [Category A] {P : A ⥤ A} (e : P ≅ 𝟭 A) (M : A) :
    P.map (e.hom.app M) = e.hom.app (P.obj M) := by
  apply (cancel_mono (e.hom.app M)).1
  exact e.hom.naturality (e.hom.app M)

/-- Composition compatibility forces identity compatibility after cancelling the two units. -/
private theorem evaluation_identity
    {A B : Type*} [Category A] [Category B] (P : A ⥤ A) (Q : B ⥤ B) (V : A ⥤ B)
    (e : P ≅ 𝟭 A) (f : Q ≅ 𝟭 B) (c : P ≅ P ⋙ P) (d : Q ≅ Q ⋙ Q)
    (q : P ⋙ V ≅ V ⋙ Q)
    (hc : ∀ M, c.hom.app M ≫ P.map (e.hom.app M) = 𝟙 _)
    (hd : ∀ N, d.hom.app N ≫ Q.map (f.hom.app N) = 𝟙 _)
    (hq : ∀ M, V.map (c.inv.app M) ≫ q.hom.app M =
      q.hom.app (P.obj M) ≫ Q.map (q.hom.app M) ≫ d.inv.app (V.obj M)) (M : A) :
    q.hom.app M ≫ f.hom.app (V.obj M) = V.map (e.hom.app M) := by
  let : Q.Faithful := Functor.Faithful.of_iso f.symm
  have hc' : c.inv.app M = P.map (e.hom.app M) := by
    apply (cancel_epi (c.hom.app M)).1
    rw [Iso.hom_inv_id_app, hc]
  have hd' : d.inv.app (V.obj M) = Q.map (f.hom.app (V.obj M)) := by
    apply (cancel_epi (d.hom.app (V.obj M))).1
    rw [Iso.hom_inv_id_app, hd]
  apply Q.map_injective
  apply (cancel_epi (q.hom.app (P.obj M))).1
  rw [Functor.map_comp, ← Category.assoc]
  have hn := q.hom.naturality (e.hom.app M)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  rw [← hn]
  simpa only [hc', hd', Category.assoc] using (hq M).symm

/-- The same cancellation with the scheme identity-composition transport retained. -/
private theorem evaluation_identity_index
    {I A B : Type*} [Category A] [Category B]
    (P : I → A ⥤ A) (Q : I → B ⥤ B) (V : A ⥤ B)
    (q : ∀ i, P i ⋙ V ≅ V ⋙ Q i) {i j : I} (h : i = j)
    (e : P j ≅ 𝟭 A) (f : Q j ≅ 𝟭 B)
    (c : P i ≅ P j ⋙ P j) (d : Q i ≅ Q j ⋙ Q j)
    (hc : ∀ M, (eqToIso (congrArg P h.symm)).hom.app M ≫
      c.hom.app M ≫ (P j).map (e.hom.app M) = 𝟙 _)
    (hd : ∀ N, (eqToIso (congrArg Q h.symm)).hom.app N ≫
      d.hom.app N ≫ (Q j).map (f.hom.app N) = 𝟙 _)
    (hq : ∀ M, V.map (c.inv.app M) ≫ (q i).hom.app M =
      (q j).hom.app ((P j).obj M) ≫ (Q j).map ((q j).hom.app M) ≫
        d.inv.app (V.obj M)) (M : A) :
    (q j).hom.app M ≫ f.hom.app (V.obj M) = V.map (e.hom.app M) := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp] at hc hd
  exact evaluation_identity (P i) (Q i) V e f c d (q i) hc hd hq M

/-- Read a normalized compositor unit as an equality of components. -/
private theorem unit_app
    {A : Type*} [Category A] {P H : A ⥤ A}
    (q : P ≅ H) (c : H ≅ P ⋙ P) (e : P ≅ 𝟭 A)
    (h : q ≪≫ c ≪≫ isoWhiskerLeft P e ≪≫ rightUnitor P = Iso.refl P) (M : A) :
    q.hom.app M ≫ c.hom.app M ≫ P.map (e.hom.app M) = 𝟙 _ := by
  rw [identity_naturality e]
  simpa only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.comp_id, Iso.refl_hom, NatTrans.id_app, Category.assoc] using
    congr_app (congrArg Iso.hom h) M

/-- Transport the ordinary inverse-image identity unit through the module equivalence. -/
private theorem finite_ordinary_unit (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) :
    eqToIso (congrArg (sfIntrinsicPullback A) (Category.id_comp (𝟙 X)).symm) ≪≫
      sfIntrinsicPullbackComp A (𝟙 X) (𝟙 X) ≪≫
      isoWhiskerLeft (sfIntrinsicPullback A (𝟙 X)) (sfIntrinsicPullbackId A X) ≪≫
      rightUnitor _ = Iso.refl _ := by
  rw [sfPullback_congr A (Category.id_comp (𝟙 X)).symm, sfIntrinsicPullbackComp]
  simp only [← Iso.trans_assoc]
  erw [← trIso_trans (sfIntrinsicModuleEquivalence X A)
    (sfIntrinsicModuleEquivalence X A)]
  have hraw := ProEtale.upperStarComp_id_left
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (𝟙 X)
  rw [hraw]
  simp only [← Iso.trans_assoc, ProEtale.upperStarCongr, eqToIso_refl, Iso.refl_trans]
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [sfIntrinsicPullbackId, trIso, sfIntrinsicTransportIso,
    sfIntrinsicTransportComp, Equivalence.funInvIdAssoc, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, isoWhiskerRight_inv, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, rightUnitor_hom_app, rightUnitor_inv_app, leftUnitor_inv_app,
    associator_hom_app, Functor.comp_obj,
    Category.assoc, Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp]
  rw [← (sfIntrinsicModuleEquivalence X A).functor.map_comp_assoc,
    ← (ProEtale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).inv.naturality]
  rw [Functor.id_map, (sfIntrinsicModuleEquivalence X A).functor.map_comp]
  simp only [sfIntrinsicPullback, sfIntrinsicTransport, Functor.comp_obj, Category.assoc,
    ← (sfIntrinsicModuleEquivalence X A).functor.map_comp_assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  exact (sfIntrinsicModuleEquivalence X A).functor_unitIso_comp _

/-- The unit equation for inverse mates transports identity cancellation to left adjoints. -/
private theorem open_identity_evaluation
    {A B : Type*} [Category A] [Category B] {L P : A ⥤ A} {K Q : B ⥤ B}
    (a : L ⊣ P) (b : K ⊣ Q) (V : A ⥤ B) (e : P ≅ 𝟭 A) (f : Q ≅ 𝟭 B)
    (q : P ⋙ V ≅ V ⋙ Q) (r : L ⋙ V ≅ V ⋙ K)
    (hq : ∀ M, q.hom.app M ≫ f.hom.app (V.obj M) = V.map (e.hom.app M))
    (hr : (mateEquiv a b).symm q.hom = r.inv) (M : A) :
    V.map ((a.leftAdjointIdIso e).hom.app M) =
      r.hom.app M ≫ (b.leftAdjointIdIso f).hom.app (V.obj M) := by
  have hu := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ q.hom) M
  change V.map (a.unit.app M) ≫ q.hom.app (L.obj M) =
    b.unit.app (V.obj M) ≫ Q.map (((mateEquiv a b).symm q.hom).app M) at hu
  rw [hr] at hu
  have hi : V.map ((a.leftAdjointIdIso e).inv.app M) =
      (b.leftAdjointIdIso f).inv.app (V.obj M) ≫ r.inv.app M := by
    rw [Adjunction.leftAdjointIdIso_inv_app, V.map_comp, ← hq]
    rw [← Category.assoc, hu, Category.assoc]
    erw [f.hom.naturality]
    simp only [Functor.id_map, Adjunction.leftAdjointIdIso_inv_app, Category.assoc]
  apply (cancel_epi (V.map ((a.leftAdjointIdIso e).inv.app M))).1
  rw [← V.map_comp, Iso.inv_hom_id_app, V.map_id, hi]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

/-- Exact localization preserves equality transport of functors. -/
private theorem map_derived_transport
    {A B I : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : I → A ⥤ B) [∀ j, (F j).Additive]
    [∀ j, PreservesFiniteLimits (F j)] [∀ j, PreservesFiniteColimits (F j)]
    {j k : I} (h : j = k) :
    (Functor.mapDerivedCategoryNatIso (eqToIso (congrArg F h))).hom =
      (eqToIso (congrArg (fun j ↦ (F j).mapDerivedCategory) h)).hom := by
  cases h
  exact Functor.mapDerivedCategoryNatIso_refl

/-- Localize the transported finite identity unit. -/
private theorem finite_derived_unit (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) (N : proEtaleDerivedCategory X A) :
    (eqToIso (congrArg (sfIntrinsicDerivedPullback A)
      (Category.id_comp (𝟙 X)).symm)).hom.app N ≫
      (sfIntrinsicDerivedPullbackComp A (𝟙 X) (𝟙 X)).hom.app N ≫
      (sfIntrinsicDerivedPullback A (𝟙 X)).map
        ((sfIntrinsicDerivedPullbackId A X).hom.app N) = 𝟙 _ := by
  have h := AlgebraicGeometry.ProEtale.StrictTower.descend_left_unit
    (sfIntrinsicPullback A (𝟙 X)) (sfIntrinsicPullback A (𝟙 X ≫ 𝟙 X))
    (sfIntrinsicPullback A (𝟙 X))
    (eqToIso (congrArg (sfIntrinsicPullback A) (Category.id_comp (𝟙 X)).symm))
    (sfIntrinsicPullbackComp A (𝟙 X) (𝟙 X)) (sfIntrinsicPullbackId A X)
    (finite_ordinary_unit A X)
  rw [map_derived_transport (sfIntrinsicPullback A)
    (Category.id_comp (𝟙 X)).symm] at h
  rw [identity_naturality]
  simpa only [sfIntrinsicDerivedPullbackComp, sfIntrinsicDerivedPullbackId,
    Iso.trans_hom, NatTrans.comp_app, whiskerLeft_app, Category.assoc,
    NatTrans.id_app] using congr_app h N

/-- Changing the right adjoint to the identity gives its normalized left identity. -/
private theorem open_identity_normalization
    {A : Type*} [Category A] {L R : A ⥤ A} (a : L ⊣ R) (e : R ≅ 𝟭 A) :
    (a.ofNatIsoRight e).leftAdjointUniq Adjunction.id = a.leftAdjointIdIso e := by
  apply Iso.ext_inv
  ext M
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointIdIso,
    conjugateIsoEquiv, conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight]

/-- Exact localization preserves the adjunction-normalized identity-open comparison. -/
private theorem finite_open_identity
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (W : Scheme.{u}) (m : ℕ) :
    (WeilConjectures.IntegralSystemRealization.finiteOpenAdj l E (𝟙 W) m).leftAdjointIdIso
      (sfIntrinsicDerivedPullbackId (Padic.coefficientExtensionRing l E (m + 1)) W) =
    Functor.mapDerivedCategoryNatIso
      (sfIntrinsicOpenId (Padic.coefficientExtensionRing l E (m + 1)) W) ≪≫
      Functor.mapDerivedCategoryIdIso _ := by
  dsimp only [WeilConjectures.IntegralSystemRealization.finiteOpenAdj,
    SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction,
    sfIntrinsicDerivedPullbackId]
  rw [← ProEtale.AmbientProperOpen.exact_left_id_localized,
    sfIntrinsicOpenId, open_identity_normalization]

namespace WeilConjectures.IntegralProjectionReduction
open IntegralSystemRealization ProperCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus
attribute [local implicit_reducible] integralCoefficientSheaf
  scalarReductionTargetDerived integralTowerHasDerivedCategory coefficientFiniteHasDerived

/-- Finite evaluation preserves the canonical identity-open cancellation, for an
arbitrary coefficient system. No integral input or operation datum occurs.

Source: fix-prop-projection-formula.proof.md, proper-coincidence normalization;
Stacks 03DI and 0941, canonical open-adjunction units.
(blueprint: lem-sf-system-identity-open-evaluation).

Proof: normalize the system identity pullback using its compositor unit. Transport
and localize the ordinary identity pullback unit to obtain the finite unit. Apply
pullback-compositor evaluation to two identity maps. Naturality and cancellation
of the invertible comparison show that pullback evaluation preserves these
identity comparisons. The specified inverse open mate then identifies evaluation
of inverse identity-open cancellation with the composite of the finite inverse
cancellation and inverse open evaluation. Invert this equation. Exact localization
identifies the finite adjunction comparison with the displayed finite open
comparison. The argument applies to arbitrary systems, including the zero system
and the initial scheme; it uses no faithfulness of finite derived evaluation. -/
theorem systemIdentityOpenEvaluation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (o : Operations C.l E) (z : Realizations C.l E D o)
    (W : Scheme.{u}) (m : ℕ) (M : System C.l E W) :
    (coefficientSequenceDerivedEvaluation C.l E W m).map
        ((openIdentity o z W).hom.app M) =
      ((o.openEvaluation (𝟙 W)).evaluation m).hom.app M ≫
        (Functor.mapDerivedCategoryNatIso
          (@sfIntrinsicOpenId (Padic.coefficientExtensionRing C.l E (m + 1)) _
            (Padic.finite_coefficientExtensionRing C.l E (m + 1)
              (Nat.le_add_left 1 m)) W) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app
            ((coefficientSequenceDerivedEvaluation C.l E W m).obj M) := by
  obtain ⟨e, he, hb⟩ := systemPushIdentityPullUnit C.l E o z.compositors z.canonicalBridge W
  have hc := unit_app _ _ e he
  have hq := evaluation_identity_index (pull C.l E)
    (sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing C.l E (m + 1)))
    (coefficientSequenceDerivedEvaluation C.l E W m)
    (fun f : W ⟶ W ↦ pullbackTensorDerivedEvaluation C.l E f m)
    (Category.id_comp (𝟙 W)) e
    (sfIntrinsicDerivedPullbackId (Padic.coefficientExtensionRing C.l E (m + 1)) W)
    (z.compositors.pullComp (𝟙 W) (𝟙 W))
    (sfIntrinsicDerivedPullbackComp (Padic.coefficientExtensionRing C.l E (m + 1))
      (𝟙 W) (𝟙 W)) hc
    (finite_derived_unit (Padic.coefficientExtensionRing C.l E (m + 1)) W)
    (systemPullbackCompositorEvaluation C.l E o z.compositors (𝟙 W) (𝟙 W) m)
  have hec : e = z.canonicalBridge.pull C.l E (𝟙 W) ≪≫
      ProEtale.SemilinearProperOpen.pId (scalarRings C.l E) (scalarTransitions C.l E) W := by
    have hh : e.symm = (z.canonicalBridge.pull C.l E (𝟙 W) ≪≫
        ProEtale.SemilinearProperOpen.pId (scalarRings C.l E)
          (scalarTransitions C.l E) W).symm := by
      apply (conjugateIsoEquiv (o.direct (𝟙 W)).adj Adjunction.id).injective
      rw [hb, Iso.trans_symm, conjugateIsoEquiv_trans]
      rfl
    simpa only [Iso.symm_symm_eq] using congrArg Iso.symm hh
  have hj : (o.extension (𝟙 W)).adj.leftAdjointIdIso e = openIdentity o z W := by
    rw [hec]
    simpa only [openIdentity, CanonicalBridge.shriek, ProEtale.SemilinearProperOpen.jId] using
      IntegralSystemRealization.identity_bridge (o.extension (𝟙 W)).adj
        (ProEtale.SemilinearProperOpen.jAdj (scalarRings C.l E) (scalarTransitions C.l E) (𝟙 W))
        (z.canonicalBridge.pull C.l E (𝟙 W))
        (ProEtale.SemilinearProperOpen.pId (scalarRings C.l E) (scalarTransitions C.l E) W)
  have h := open_identity_evaluation (o.extension (𝟙 W)).adj (finiteOpenAdj C.l E (𝟙 W) m)
    (coefficientSequenceDerivedEvaluation C.l E W m) e
    (sfIntrinsicDerivedPullbackId (Padic.coefficientExtensionRing C.l E (m + 1)) W)
    (pullbackTensorDerivedEvaluation C.l E (𝟙 W) m)
    ((o.openEvaluation (𝟙 W)).evaluation m) hq ((o.openEvaluation (𝟙 W)).transpose m) M
  rw [hj, finite_open_identity] at h
  exact h
end WeilConjectures.IntegralProjectionReduction
