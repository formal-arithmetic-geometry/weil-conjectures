/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.DeligneLaumon.ConstantFieldRestriction
public import WeilConjectures.WeilSheaf.StalkFrobenius
import WeilConjectures.WeilSheaf.BaseChangeField.Coherence
import Sheaf.DeligneLaumon.ConstantFieldTransportComparison

/-! # Iterated structure maps of source constant-field transport

Source: blueprint `thm-zl-real-mixed-by-curves`, first paragraph, and the
ordered iteration in `def-weil-local-frobenius-trace`.
(blueprint: lem-zl-source-constant-field-transport-structure).
-/

@[expose] public section
set_option autoImplicit false
universe v u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.WeilSheaf
open ProEtale

section UnderlyingIteration

-- Keep module-action data out of the underlying-map calculations.
attribute [local irreducible] adicConstantSheaf upperStar lowerStar
  upperStarIsoLowerStarInv

private lemma pushforward_add_of_pullback
    {Z : Scheme.{u}} {l : ℕ} [Fact l.Prime] (a b c : Aut Z)
    (h : b.hom ≫ a.hom = c.hom) (hi : a.inv ≫ b.inv = c.inv)
    (M : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l))
    (sa : (a.inv)_*[_].obj M ⟶ M) (sb : (b.inv)_*[_].obj M ⟶ M)
    (sc : (c.inv)_*[_].obj M ⟶ M)
    (hs : (upperStarFactor _ h).hom.app M ≫
      (b.hom)^*[_].map ((upperStarIsoLowerStarInv _ a).hom.app M ≫ sa) ≫
      (upperStarIsoLowerStarInv _ b).hom.app M ≫ sb =
      (upperStarIsoLowerStarInv _ c).hom.app M ≫ sc) :
    (lowerStarFactor _ hi).inv.app M ≫ (b.inv)_*[_].map sa ≫ sb = sc := by
  have L := upperStarIsoLowerStarInv_hom_app_trans (WeilCoefficients.{u} l)
    b a c h hi M
  have n := (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) b).hom.naturality sa
  simp only [Functor.map_comp, Category.assoc] at hs
  erw [reassoc_of% n, ← reassoc_of% L] at hs
  exact (cancel_epi ((upperStarIsoLowerStarInv (WeilCoefficients.{u} l) c).hom.app M)).mp hs

private lemma lowerStar_factor_right_unit {Z : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    (t : Z ⟶ Z) (M N : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l))
    (f : (t)_*[_].obj M ⟶ N) :
    (lowerStarFactor _ (Category.comp_id t)).inv.app M ≫
      (𝟙 Z)_*[_].map f ≫ (lowerStarId _ Z).hom.app N = f := by
  have n : (𝟙 Z)_*[_].map f ≫ (lowerStarId _ Z).hom.app N =
      (lowerStarId _ Z).hom.app ((t)_*[_].obj M) ≫ f :=
    (lowerStarId (WeilCoefficients.{u} l) Z).hom.naturality f
  rw [n]
  have h : lowerStarFactor (WeilCoefficients.{u} l) (Category.comp_id t) =
      Functor.isoWhiskerLeft (t)_*[_] (lowerStarId _ Z) ≪≫ (t)_*[_].rightUnitor := by
    rw [← lowerStarComp_trans_lowerStarCongr, lowerStarComp_id_right]
    simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  rw [h]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.id_comp,
    Iso.inv_hom_id_app_assoc]

private lemma powIso_zero_hom
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (F : WeilSheaf k l X) :
    (F.frobeniusPowIso 0).hom.hom =
      (lowerStarId (WeilCoefficients.{u} l) _).hom.app F.obj.carrier.X := by
  simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Mod.comp_hom',
    adicLowerStarCongr_hom_app_hom, adicLowerStarId_hom_app_hom]
  change (lowerStarCongr _ (rfl : (𝟙 _) = 𝟙 _)).hom.app _ ≫
    (lowerStarId _ _).hom.app _ = _
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

-- Fix the source in the sheaf category to keep adic module actions out of conversion.
@[irreducible] private noncomputable def iterateMap
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (F : WeilSheaf k l X) (m : ℕ) :
    (((X ↘ Spec (CommRingCat.of k)).geometricGaloisFrobenius ^ m).inv)_*[
      WeilCoefficients.{u} l].obj F.obj.carrier.X ⟶ F.obj.carrier.X :=
  (F.frobeniusPowIso m).hom.hom

private lemma frobeniusPowStr_hom_hom
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (F : WeilSheaf k l X) (m : ℕ) :
    F.frobeniusPowStr m =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
        ((X ↘ Spec (CommRingCat.of k)).geometricGaloisFrobenius ^ m)).hom.app
          F.obj.carrier.X ≫ iterateMap F m := by
  unfold iterateMap
  rfl

private lemma pow_hom_add
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (F : WeilSheaf k l X) (a b : ℕ)
    (hi : ((X ↘ Spec (CommRingCat.of k)).geometricGaloisFrobenius ^ a).inv ≫
      ((X ↘ Spec (CommRingCat.of k)).geometricGaloisFrobenius ^ b).inv =
      ((X ↘ Spec (CommRingCat.of k)).geometricGaloisFrobenius ^ (a + b)).inv) :
    (lowerStarFactor _ hi).inv.app F.obj.carrier.X ≫
      (((X ↘ Spec (CommRingCat.of k)).geometricGaloisFrobenius ^ b).inv)_*[_].map
        (F.frobeniusPowIso a).hom.hom ≫ (F.frobeniusPowIso b).hom.hom =
      (F.frobeniusPowIso (a + b)).hom.hom := by
  cases b with
  | succ b =>
    have he := (X ↘ Spec (CommRingCat.of k)).geometricGaloisFrobenius.pow_hom_comp_pow_hom
      a (b + 1)
    apply pushforward_add_of_pullback _ _ _ he hi F.obj.carrier.X
      (F.frobeniusPowIso a).hom.hom (F.frobeniusPowIso (b + 1)).hom.hom
      (F.frobeniusPowIso (a + (b + 1))).hom.hom
    simpa only [frobeniusPowStr, Functor.map_comp, Category.assoc,
      AdicSheaf.forget, Mod.forget] using
      upperStarFactor_hom_app_comp_frobeniusPowStr_add F a (b + 1)
        (Nat.succ_le_succ (Nat.zero_le b)) he
  | zero =>
    rw [powIso_zero_hom]
    exact lowerStar_factor_right_unit
      ((X ↘ Spec (CommRingCat.of k)).geometricGaloisFrobenius ^ a).inv
      F.obj.carrier.X F.obj.carrier.X (F.frobeniusPowIso a).hom.hom

private lemma postcompose_eq {C : Type v} [Category C] {A B D : C}
    {f g : A ⟶ B} (h : f = g) (k : B ⟶ D) : f ≫ k = g ≫ k :=
  congrArg (fun p ↦ p ≫ k) h

section TransportCalculation

variable {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₁))]
  (θ : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Y ↘ Spec (CommRingCat.of k₁)).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius.hom =
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)

include hθ in
private lemma transport_inverse_power (m : ℕ) :
    θ.hom ≫ ((Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius ^ m).inv =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * m)).inv ≫ θ.hom := by
  have h := ProEtaleWeilSheaf.hom_comp_geometricGaloisFrobenius_inv θ r hθ
  induction m with
  | zero =>
    simp only [Nat.mul_zero, pow_zero]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ m ih =>
    rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv, ← Category.assoc, ih, Category.assoc, h,
      ← Category.assoc, Nat.mul_succ, pow_add, Aut.Aut_mul_def, Iso.trans_inv]

private lemma restriction_carrier_app (F : WeilSheaf k₀ l X)
    {S T : Sheaf (Scheme.ProEt.topology
        (Y ↘ Spec (CommRingCat.of k₁)).geometricFiber) (WeilCoefficients.{u} l) ⥤
      Sheaf (Scheme.ProEt.topology
        (Y ↘ Spec (CommRingCat.of k₁)).geometricFiber) (WeilCoefficients.{u} l)}
    (η : S ⟶ T) :
    η.app ((constantFieldRestriction θ r hθ).obj F).obj.carrier.X =
      η.app ((θ.hom)_*[WeilCoefficients.{u} l].obj F.obj.carrier.X) := by
  rfl

omit [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)] in
private lemma transport_comparison_eq :
    ProEtaleWeilSheaf.transportCommIso (l := l) θ r hθ =
      adicLowerStarSquareIso l
        (ProEtaleWeilSheaf.hom_comp_geometricGaloisFrobenius_inv θ r hθ) := by
  rfl

private lemma restriction_structure_hom (F : WeilSheaf k₀ l X) :
    (((constantFieldRestriction θ r hθ).obj F).obj.str.hom).hom =
      (lowerStarFactor _
        (ProEtaleWeilSheaf.hom_comp_geometricGaloisFrobenius_inv θ r hθ)).hom.app
          F.obj.carrier.X ≫
      (lowerStarFactor _ (rfl :
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).inv ≫ θ.hom =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).inv ≫ θ.hom)
        ).inv.app F.obj.carrier.X ≫
      (θ.hom)_*[_].map (F.frobeniusPowIso r).hom.hom := by
  have ht := ProEtaleWeilSheaf.transport_obj_str θ r hθ F.obj
  conv_rhs at ht => rw [transport_comparison_eq θ r hθ]
  have hs := congrArg (fun f ↦ f.hom.hom) ht
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Mod.comp_hom',
    adicLowerStar_map_hom] at hs
  change (((ProEtaleWeilSheaf.transport θ r hθ).obj F.obj).str.hom).hom = _
  rw [hs]
  rw [adicLowerStarSquareIso_hom_app_hom]
  have he := congrArg (fun f ↦ f.hom.hom) (frobeniusPowIso_eq F r)
  rw [he]
  simp only [Category.assoc]

private lemma restriction_powIso_hom (F : WeilSheaf k₀ l X) (m : ℕ) :
    (((constantFieldRestriction θ r hθ).obj F).frobeniusPowIso m).hom.hom =
      (lowerStarFactor _ (transport_inverse_power θ r hθ m)).hom.app F.obj.carrier.X ≫
      (lowerStarFactor _ (rfl :
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * m)).inv ≫ θ.hom =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * m)).inv ≫ θ.hom)
        ).inv.app F.obj.carrier.X ≫
      (θ.hom)_*[_].map (F.frobeniusPowIso (r * m)).hom.hom := by
  induction m with
  | zero =>
    have h0 := powIso_zero_hom ((constantFieldRestriction θ r hθ).obj F)
    have h1 := powIso_zero_hom F
    simp only [Nat.mul_zero]
    rw [h0, h1]
    exact (lowerStarFactor_exchange_id (WeilCoefficients.{u} l) θ.hom _
      (transport_inverse_power θ r hθ 0) rfl F.obj.carrier.X).symm
  | succ m ih =>
    have ha : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * m)).inv ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).inv =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * (m + 1))).inv := by
      rw [Nat.mul_succ, pow_add, Aut.Aut_mul_def, Iso.trans_inv]
    have hb : ((Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius ^ m).inv ≫
        (Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius.inv =
        ((Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius ^ (m + 1)).inv := by
      rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]
    have hrec := forget_map_frobeniusPowIso_succ_hom
      ((constantFieldRestriction θ r hθ).obj F) m hb.symm
    simp only [AdicSheaf.forget, Mod.forget] at hrec
    rw [hrec]
    simp only [reassoc_of% lowerStarCongr_hom_app_comp_lowerStarComp_inv_app_eq]
    rw [ih, restriction_structure_hom θ r hθ F]
    simp only [Functor.map_comp, Category.assoc]
    let e := lowerStarFactor (WeilCoefficients.{u} l)
      (ProEtaleWeilSheaf.hom_comp_geometricGaloisFrobenius_inv θ r hθ) ≪≫
      (lowerStarFactor (WeilCoefficients.{u} l) (rfl :
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).inv ≫ θ.hom =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).inv ≫ θ.hom)).symm
    have nat := e.hom.naturality (F.frobeniusPowIso (r * m)).hom.hom
    dsimp only [e] at nat
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_map,
      adicLowerStar_obj_X] at nat
    erw [reassoc_of% nat]
    have key := lowerStarFactor_exchange_comp (WeilCoefficients.{u} l) θ.hom
      _ _ _ _ _ _ _ _ _ ha hb
      (ProEtaleWeilSheaf.hom_comp_geometricGaloisFrobenius_inv θ r hθ) rfl
      (transport_inverse_power θ r hθ m) rfl
      (transport_inverse_power θ r hθ (m + 1)) rfl F.obj.carrier.X
    simp only [Functor.map_comp, Category.assoc] at key
    erw [reassoc_of% key]
    simp only [← Functor.map_comp]
    have add := pow_hom_add F (r * m) r (by
      rw [pow_add, Aut.Aut_mul_def, Iso.trans_inv])
    simpa only [Nat.mul_succ] using congrArg (fun f ↦
      (lowerStarFactor _ (transport_inverse_power θ r hθ (m + 1))).hom.app
        F.obj.carrier.X ≫
      (lowerStarFactor _ (rfl :
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * (m + 1))).inv ≫
          θ.hom =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * (m + 1))).inv ≫
          θ.hom)).inv.app F.obj.carrier.X ≫ (θ.hom)_*[_].map f) add

private lemma restriction_iterateMap (F : WeilSheaf k₀ l X) (m : ℕ) :
    iterateMap ((constantFieldRestriction θ r hθ).obj F) m =
      (lowerStarFactor _ (transport_inverse_power θ r hθ m)).hom.app F.obj.carrier.X ≫
      (lowerStarFactor _ (rfl :
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * m)).inv ≫ θ.hom =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * m)).inv ≫ θ.hom)
        ).inv.app F.obj.carrier.X ≫
      (θ.hom)_*[_].map (iterateMap F (r * m)) := by
  unfold iterateMap
  exact restriction_powIso_hom θ r hθ F m

end TransportCalculation
end UnderlyingIteration

section CarrierCoherence

attribute [local irreducible] adicConstantSheaf upperStar lowerStar
  upperStarIsoLowerStarInv upperStarComp lowerStarComp
  upperStarFactor lowerStarFactor upperStarCongr

private lemma carrier_comparison_square (A : Type v) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {P Q : Scheme.{u}}
    (θ : P ≅ Q) (a : P ≅ P) (b : Q ≅ Q)
    (hc : b.hom ≫ θ.inv = θ.inv ≫ a.hom)
    (hi : θ.hom ≫ b.inv = a.inv ≫ θ.hom)
    (M : Sheaf (Scheme.ProEt.topology P) A) :
    (upperStarComp _ b.hom θ.inv).hom.app M ≫
      (b.hom)^*[_].map ((upperStarIsoLowerStarInv _ θ.symm).hom.app M) ≫
      (upperStarIsoLowerStarInv _ b).hom.app ((θ.hom)_*[_].obj M) ≫
      (lowerStarFactor _ hi).hom.app M ≫
      (lowerStarFactor _ (rfl : a.inv ≫ θ.hom = a.inv ≫ θ.hom)).inv.app M =
    (upperStarCongr _ hc).hom.app M ≫
      (upperStarComp _ θ.inv a.hom).hom.app M ≫
      (θ.inv)^*[_].map ((upperStarIsoLowerStarInv _ a).hom.app M) ≫
      (upperStarIsoLowerStarInv _ θ.symm).hom.app ((a.inv)_*[_].obj M) := by
  have H := upperStarIsoLowerStarInv_exchange A θ.symm a b hc hi
  simp only [Iso.symm_hom, Iso.symm_inv] at H
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    NatTrans.congr_app H M

/-- The canonical comparison between inverse pullback and the actual carrier
of source constant-field transport.

Source: blueprint `thm-zl-real-mixed-by-curves`, first paragraph.
(blueprint: lem-zl-source-constant-field-transport-structure).
This is the canonical pullback/pushforward isomorphism, with its target written
as the carrier of the constructed restriction. -/
noncomputable def constantFieldRestrictionCarrierIso
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₁))]
    (θ : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      (Y ↘ Spec (CommRingCat.of k₁)).geometricFiber) (r : ℕ)
    (hθ : θ.hom ≫ (Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
    (F : WeilSheaf k₀ l X) :
    (θ.inv)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X ≅
      ((constantFieldRestriction θ r hθ).obj F).obj.carrier.X :=
  (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) θ.symm).app F.obj.carrier.X

-- Clients use the displayed carrier interface without unfolding the transport construction.
attribute [irreducible] constantFieldRestrictionCarrierIso

private lemma carrierIso_hom
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₁))]
    (θ : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      (Y ↘ Spec (CommRingCat.of k₁)).geometricFiber) (r : ℕ)
    (hθ : θ.hom ≫ (Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
    (F : WeilSheaf k₀ l X) :
    (constantFieldRestrictionCarrierIso θ r hθ F).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) θ.symm).hom.app F.obj.carrier.X := by
  unfold constantFieldRestrictionCarrierIso
  rfl

/-- The canonical pullback-to-pushforward comparison intertwines the iterated
structure maps of source constant-field transport.

Source: blueprint `thm-zl-real-mixed-by-curves`, first paragraph, and the ordered
iteration in `def-weil-local-frobenius-trace`.
(blueprint: lem-zl-source-constant-field-transport-structure).

Proof: Write the carrier comparison as the canonical identification
`(θ⁻¹)^* F ≅ θ_* F`. For the first iterate, expand `transport_obj_str`:
its exchange isomorphism identifies the pullback along the new Frobenius
with the old r-fold pullback. Compatibility of the pullback/pushforward
identification with composition, specifically
`upperStarIsoLowerStarInv_hom_app_trans` after forgetting the adic module maps,
gives the displayed first-iterate square. For iterate zero,
both structure maps are the pullback identity comparison, so the square is
its naturality square. If r is zero, cancellation of theta in hθ makes the new
Frobenius the identity.
The transported structure and all its iterates are then the canonical identity
pullback comparisons, so the same unit coherence proves the equation. For
positive r, induct on m. Expand the successor iteration
on both sides, using `upperStarFactor_hom_app_comp_frobeniusPowStr_add`
for the old iterates r*m and r.
Move the carrier comparison through the new Frobenius pullback by the first
iterate square, and substitute the induction hypothesis. Associativity of the
pullback compositors (`upperStarFactor_hom_app_assoc`) identifies the two
composites; naturality moves the old
iterated structure map through that compositor. The equality of scheme maps
is hc, so congruence introduces exactly its displayed pullback comparison.
No stalks, finite points, residue degrees or choice of geometric lifts enter. -/
theorem frobeniusPowStr_constantFieldRestriction
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₁))]
    (θ : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      (Y ↘ Spec (CommRingCat.of k₁)).geometricFiber) (r : ℕ)
    (hθ : θ.hom ≫ (Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
    (F : WeilSheaf k₀ l X) (m : ℕ)
    (hc : ((Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius ^ m).hom ≫ θ.inv =
      θ.inv ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom) :
    (upperStarComp _ _ _).hom.app F.obj.carrier.X ≫
      (((Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius ^ m).hom)^*[_].map
        (constantFieldRestrictionCarrierIso θ r hθ F).hom ≫
          ((constantFieldRestriction θ r hθ).obj F).frobeniusPowStr m =
    (upperStarCongr _ hc).hom.app F.obj.carrier.X ≫
      (upperStarComp _ _ _).hom.app F.obj.carrier.X ≫
      (θ.inv)^*[_].map (F.frobeniusPowStr (r * m)) ≫
      (constantFieldRestrictionCarrierIso θ r hθ F).hom := by
  simp only [carrierIso_hom, frobeniusPowStr_hom_hom, Functor.map_comp, Category.assoc]
  rw [restriction_iterateMap θ r hθ F m]
  have n := (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) θ.symm).hom.naturality
    (iterateMap F (r * m))
  simp only [Iso.symm_hom, Iso.symm_inv] at n
  rw [n]
  erw [restriction_carrier_app θ r hθ F
    (upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
      ((Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius ^ m)).hom]
  simpa only [Category.assoc] using postcompose_eq
    (carrier_comparison_square (WeilCoefficients.{u} l) θ
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * m))
      ((Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius ^ m)
      hc (transport_inverse_power θ r hθ m) F.obj.carrier.X)
    ((θ.hom)_*[_].map (iterateMap F (r * m)))

end CarrierCoherence
end AlgebraicGeometry.WeilSheaf
