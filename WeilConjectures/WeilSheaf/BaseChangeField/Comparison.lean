/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.WeilSheaf.BaseChangeField.Coherence
public import WeilConjectures.WeilSheaf.BaseChangeField.Transport
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# Transport of Weil sheaves commutes with pushforward and preserves `ℚ̄_ℓ`

Let `θ : X̄ ≅ X̄'` and `θ_Y : Ȳ ≅ Ȳ'` identify the geometric fibers of `k₀`-schemes `X`, `Y` with
those of `k₀'`-schemes `X'`, `Y'`, intertwining the geometric Galois Frobenii of `X'`, `Y'` with
the `r`-th powers of those of `X`, `Y`. This file shows:

- `AlgebraicGeometry.ProEtaleWeilSheaf.lowerStar_obj_frobeniusPowIso`: the iterated Weil
  structure `φ_m` of a pushforward `φ_* K` is the pushforward of the iterated Weil structure of
  `K`, up to the exchange isomorphism `(Frᵐ)^* φ̄_* ≅ φ̄_* (Frᵐ)^*`;
- `AlgebraicGeometry.ProEtaleWeilSheaf.transportLowerStarIso`: for morphisms `φ : X ⟶ Y`,
  `φ' : X' ⟶ Y'` whose base changes commute with `θ`, `θ_Y`, transporting and pushing forward
  commute;
- `AlgebraicGeometry.ProEtaleWeilSheaf.adicConstantTransportIso`: the transport of the constant
  Weil sheaf `ℚ̄_ℓ` on `X` is the constant Weil sheaf on `X'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

noncomputable section

namespace AlgebraicGeometry

open ProEtale

/-- The base change `φ̄` commutes with the inverses of the powers of the geometric Galois
Frobenii. -/
@[reassoc]
lemma Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow_inv {k : Type u} [Field k]
    [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)} {g : Y₀ ⟶ Spec (.of k)}
    (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) (m : ℕ) :
    geometricFiberMap φ h ≫ (g.geometricGaloisFrobenius ^ m).inv =
      (f.geometricGaloisFrobenius ^ m).inv ≫ geometricFiberMap φ h := by
  induction m with
  | zero => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ m ih =>
    rw [pow_succ, pow_succ, Aut.Aut_mul_def, Aut.Aut_mul_def, Iso.trans_inv, Iso.trans_inv,
      reassoc_of% ih, geometricFiberMap_comp_geometricGaloisFrobenius_inv, Category.assoc]

section Unit

variable {l : ℕ} [Fact l.Prime]

/-- The identifications `e_* ℚ̄_ℓ ≅ ℚ̄_ℓ` along isomorphisms are compatible with composition. -/
lemma ProEtale.adicLowerStarUnitIso_comp {X Y W : Scheme.{u}} (e₁ : X ≅ Y) (e₂ : Y ≅ W) :
    (e₂.hom)_*ᵃ[l].map (adicLowerStarUnitIso l e₁).hom ≫ (adicLowerStarUnitIso l e₂).hom =
      (adicLowerStarComp l e₁.hom e₂.hom).hom.app _ ≫ (adicLowerStarUnitIso l (e₁ ≪≫ e₂)).hom := by
  have h : (adicLowerStarUnitIso l (e₁ ≪≫ e₂)).inv.hom =
      (adicLowerStarUnitIso l e₂).inv.hom ≫
        (e₂.hom)_*[WeilCoefficients.{u} l].map (adicLowerStarUnitIso l e₁).inv.hom ≫
          (lowerStarComp (WeilCoefficients.{u} l) e₁.hom e₂.hom).hom.app _ :=
    (adicConstantSheafToLowerStar_comp l e₁.hom e₂.hom).symm
  have h' : (adicLowerStarUnitIso l (e₁ ≪≫ e₂)).inv =
      (adicLowerStarUnitIso l e₂).inv ≫ (e₂.hom)_*ᵃ[l].map (adicLowerStarUnitIso l e₁).inv ≫
        (adicLowerStarComp l e₁.hom e₂.hom).hom.app _ :=
    Mod.hom_ext _ _ h
  have key : ((e₂.hom)_*ᵃ[l].mapIso (adicLowerStarUnitIso l e₁) ≪≫ adicLowerStarUnitIso l e₂).symm =
      ((adicLowerStarComp l e₁.hom e₂.hom).app _ ≪≫ adicLowerStarUnitIso l (e₁ ≪≫ e₂)).symm := by
    ext1
    simp only [Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
    rw [h']
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  exact congrArg (fun e ↦ e.symm.hom) key

/-- The identification `e_* ℚ̄_ℓ ≅ ℚ̄_ℓ` depends only on `e.hom`. -/
lemma ProEtale.adicLowerStarCongr_hom_app_comp_adicLowerStarUnitIso_hom {X Y : Scheme.{u}}
    {e e' : X ≅ Y} (h : e.hom = e'.hom) :
    (adicLowerStarCongr l h).hom.app _ ≫ (adicLowerStarUnitIso l e').hom =
      (adicLowerStarUnitIso l e).hom := by
  obtain rfl : e = e' := Iso.ext h
  apply Mod.hom_ext
  rw [Mod.comp_hom', adicLowerStarCongr_hom_app_hom, lowerStarCongr_rfl]
  exact Category.id_comp _

/-- The identification `(𝟙 X)_* ℚ̄_ℓ ≅ ℚ̄_ℓ` is the identity isomorphism `(𝟙 X)_* ≅ 𝟭`. -/
lemma ProEtale.adicLowerStarId_hom_app_unit (X : Scheme.{u}) :
    (adicLowerStarId l X).hom.app (AdicSheaf.unit l X) =
      (adicLowerStarUnitIso l (Iso.refl X)).hom := by
  rw [← cancel_epi (adicLowerStarUnitIso l (Iso.refl X)).inv, Iso.inv_hom_id]
  apply Mod.hom_ext
  rw [Mod.comp_hom', adicLowerStarId_hom_app_hom]
  exact adicConstantSheafToLowerStar_id l X

/-- The identification `(Aᵐ')_* ℚ̄_ℓ ≅ ℚ̄_ℓ` for `A.hom = 𝟙` is the identity isomorphism. -/
lemma ProEtale.adicLowerStarCongr_hom_app_comp_adicLowerStarId_hom_app_unit {X : Scheme.{u}}
    (A : X ≅ X) (h : A.hom = 𝟙 X) :
    (adicLowerStarCongr l h).hom.app _ ≫ (adicLowerStarId l X).hom.app (AdicSheaf.unit l X) =
      (adicLowerStarUnitIso l A).hom := by
  rw [adicLowerStarId_hom_app_unit]
  exact adicLowerStarCongr_hom_app_comp_adicLowerStarUnitIso_hom (e := A) (e' := Iso.refl X) h

/-- The identifications `e_* ℚ̄_ℓ ≅ ℚ̄_ℓ` along `C = A ≫ B` are compatible with composition. -/
lemma ProEtale.adicLowerStarUnitIso_comp' {X : Scheme.{u}} (A B C : X ≅ X)
    (h : C.hom = A.hom ≫ B.hom) :
    (adicLowerStarCongr l h).hom.app _ ≫ (adicLowerStarComp l A.hom B.hom).inv.app _ ≫
        (B.hom)_*ᵃ[l].map (adicLowerStarUnitIso l A).hom ≫ (adicLowerStarUnitIso l B).hom =
      (adicLowerStarUnitIso l C).hom := by
  rw [adicLowerStarUnitIso_comp A B, Iso.inv_hom_id_app_assoc]
  exact adicLowerStarCongr_hom_app_comp_adicLowerStarUnitIso_hom (e := C) (e' := A ≪≫ B) h

/-- The transport of the identification `G_* ℚ̄_ℓ ≅ ℚ̄_ℓ` along an isomorphism `θ` with
`θ ≫ G' = G ≫ θ` is the identification `G'_* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
lemma ProEtale.adicLowerStarUnitIso_transport {Z Z' : Scheme.{u}} (θ : Z ≅ Z') (G : Z ≅ Z)
    (G' : Z' ≅ Z') (h : θ.hom ≫ G'.hom = G.hom ≫ θ.hom) :
    (G'.hom)_*ᵃ[l].map (adicLowerStarUnitIso l θ).inv ≫
        (adicLowerStarSquareIso l h).hom.app (AdicSheaf.unit l Z) ≫
        (θ.hom)_*ᵃ[l].map (adicLowerStarUnitIso l G).hom =
      (adicLowerStarUnitIso l G').hom ≫ (adicLowerStarUnitIso l θ).inv := by
  rw [← cancel_mono (adicLowerStarUnitIso l θ).hom, Category.assoc, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← cancel_epi ((G'.hom)_*ᵃ[l].map (adicLowerStarUnitIso l θ).hom),
    ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp,
    adicLowerStarUnitIso_comp G θ, adicLowerStarUnitIso_comp θ G']
  simp only [adicLowerStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  exact adicLowerStarCongr_hom_app_comp_adicLowerStarUnitIso_hom (e := θ ≪≫ G') (e' := G ≪≫ θ) h

end Unit

namespace ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

section FrobeniusPowIso

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] (K : ProEtaleWeilSheaf k₀ l X)

lemma frobeniusPowIso_zero
    (h : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv = 𝟙 _) :
    K.frobeniusPowIso 0 = (adicLowerStarCongr l h).app _ ≪≫ (adicLowerStarId l _).app _ :=
  rfl

lemma frobeniusPowIso_succ (m : ℕ)
    (h : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).inv =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv) :
    K.frobeniusPowIso (m + 1) = (adicLowerStarCongr l h).app _ ≪≫
      (adicLowerStarComp l _ _).symm.app _ ≪≫
      (WeilSheaf.frobeniusPullback k₀ l X).mapIso (K.frobeniusPowIso m) ≪≫ K.str :=
  rfl

end FrobeniusPowIso

section LowerStar

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

set_option maxHeartbeats 1600000 in
-- The Weil structure of the pushforward unfolds through several module-object isomorphisms.
/-- The Weil structure of a pushforward is the pushforward of the Weil structure, up to the
exchange isomorphism `Fr_Y^* φ̄_* ≅ φ̄_* Fr_X^*`. -/
lemma lowerStar_obj_str (K : ProEtaleWeilSheaf k₀ l X) :
    ((lowerStar k₀ l φ).obj K).str =
      (adicLowerStarSquareIso l (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv
        φ (comp_over φ _))).app K.carrier ≪≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*ᵃ[l].mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ _

set_option maxHeartbeats 1600000 in
-- The Weil structures of pushforwards unfold through several module-object isomorphisms.
/-- The iterated Weil structure `φ_m : (Frᵐ)^* φ_* K ≅ φ_* K` of a pushforward is the pushforward
of the iterated Weil structure of `K`, up to the exchange isomorphism
`(Fr_Yᵐ)^* φ̄_* ≅ φ̄_* (Fr_Xᵐ)^*`. -/
theorem lowerStar_obj_frobeniusPowIso (K : ProEtaleWeilSheaf k₀ l X) (m : ℕ) :
    ((lowerStar k₀ l φ).obj K).frobeniusPowIso m =
      (adicLowerStarSquareIso l
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow_inv φ (comp_over φ _)
          m)).app K.carrier ≪≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*ᵃ[l].mapIso (K.frobeniusPowIso m) := by
  induction m with
  | zero =>
    ext1
    rw [frobeniusPowIso_zero _ (by rw [pow_zero]; rfl), frobeniusPowIso_zero _ (by rw [pow_zero]; rfl)]
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    exact (adicLowerStarSquareIso_id _ _ _ (by rw [pow_zero]; rfl) (by rw [pow_zero]; rfl) _
      K.carrier).symm
  | succ m ih =>
    ext1
    rw [frobeniusPowIso_succ _ _ (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]),
      frobeniusPowIso_succ _ _ (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]), ih,
      lowerStar_obj_str]
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc]
    have nat := (adicLowerStarSquareIso l
      (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ (comp_over φ _))).hom.naturality
        (K.frobeniusPowIso m).hom
    simp only [Functor.comp_map] at nat
    rw [reassoc_of% nat]
    have key := adicLowerStarSquareIso_comp (Scheme.Hom.geometricFiberMap φ (comp_over φ _))
      _ _ _ _ _ _ (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv])
      (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv])
      (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ (comp_over φ _))
      (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow_inv φ (comp_over φ _) m)
      (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow_inv φ (comp_over φ _)
        (m + 1)) K.carrier
    erw [reassoc_of% key]
    simp only [Functor.map_comp, Category.assoc]

end LowerStar

section Transport

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  {k₀' : Type u} [Field k₀'] [Finite k₀'] {X' Y' : Scheme.{u}}
  [X'.Over (Spec (CommRingCat.of k₀'))] [Y'.Over (Spec (CommRingCat.of k₀'))]
  (θ : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (X' ↘ Spec (CommRingCat.of k₀')).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (X' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.hom =
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)

lemma transportCommIso_eq :
    transportCommIso (l := l) θ r hθ =
      adicLowerStarSquareIso l (hom_comp_geometricGaloisFrobenius_inv θ r hθ) :=
  rfl

variable (θY : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber)
  (hθY : θY.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.hom =
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θY.hom)
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
  (φ' : X' ⟶ Y') [φ'.IsOver (Spec (CommRingCat.of k₀'))]
  (hsq : θ.hom ≫ Scheme.Hom.geometricFiberMap φ' (comp_over φ' _) =
    Scheme.Hom.geometricFiberMap φ (comp_over φ _) ≫ θY.hom)

include hsq in
/-- Transporting along the identifications `θ`, `θ_Y` of geometric fibers commutes with the
pushforward along morphisms `φ : X ⟶ Y` and `φ' : X' ⟶ Y'` whose base changes commute with them:
on underlying sheaves, `φ̄'_* θ_* K ≅ (θ ≫ φ̄')_* K = (φ̄ ≫ θ_Y)_* K ≅ θ_Y_* φ̄_* K`. -/
def transportLowerStarIso :
    transport (l := l) θ r hθ ⋙ lowerStar k₀' l φ' ≅ lowerStar k₀ l φ ⋙ transport θY r hθY :=
  NatIso.ofComponents (fun K ↦ IsoAlgebra.isoMk ((adicLowerStarSquareIso l hsq).app K.carrier)
    (by
      dsimp only [Functor.comp_obj]
      rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, transport_obj_str, lowerStar_obj_str,
        transport_obj_str, lowerStar_obj_frobeniusPowIso, transportCommIso_eq,
        transportCommIso_eq]
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
        Category.assoc]
      have nat := (adicLowerStarSquareIso l hsq).hom.naturality (K.frobeniusPowIso r).hom
      simp only [Functor.comp_map] at nat
      rw [nat]
      have cube := (adicLowerStarSquareIso_cube θ.hom θY.hom
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))
        (Scheme.Hom.geometricFiberMap φ' (comp_over φ' _)) _ _ _ _ hsq
        (hom_comp_geometricGaloisFrobenius_inv θ r hθ)
        (hom_comp_geometricGaloisFrobenius_inv θY r hθY)
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow_inv φ (comp_over φ _) r)
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ' (comp_over φ' _))
        K.carrier)
      simp only [Category.assoc] at cube
      convert cube =≫ _ using 3))
    (fun f ↦ IsoAlgebra.hom_ext ((adicLowerStarSquareIso l hsq).hom.naturality f.hom.f))

include hsq in
lemma transportLowerStarIso_hom_app_hom_f (K : ProEtaleWeilSheaf k₀ l X) :
    ((transportLowerStarIso θ r hθ θY hθY φ φ' hsq).hom.app K).hom.f =
      (adicLowerStarSquareIso l hsq).hom.app K.carrier :=
  rfl

end Transport

section Constant

set_option maxHeartbeats 1600000 in
-- The constant Weil sheaf unfolds through module-object isomorphisms.
variable (k₀ l) in
/-- The iterated Weil structure of the constant Weil sheaf is the identification
`(Frᵐ⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
lemma adicConstant_frobeniusPowIso (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (m : ℕ) :
    (adicConstant k₀ l X).frobeniusPowIso m =
      adicLowerStarUnitIso l ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).symm := by
  induction m with
  | zero =>
    ext1
    rw [frobeniusPowIso_zero _ (by rw [pow_zero]; rfl)]
    exact adicLowerStarCongr_hom_app_comp_adicLowerStarId_hom_app_unit _ _
  | succ m ih =>
    ext1
    rw [frobeniusPowIso_succ _ _ (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]), ih]
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    exact adicLowerStarUnitIso_comp' _ _ _ _

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {k₀' : Type u} [Field k₀'] [Finite k₀'] {X' : Scheme.{u}}
  [X'.Over (Spec (CommRingCat.of k₀'))]
  (θ : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (X' ↘ Spec (CommRingCat.of k₀')).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (X' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.hom =
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)

set_option maxHeartbeats 1600000 in
-- The constant Weil sheaf unfolds through module-object isomorphisms.
/-- The transport of the constant Weil sheaf `ℚ̄_ℓ` on `X` along `θ` is the constant Weil sheaf
on `X'`: on underlying sheaves, `ℚ̄_ℓ ≅ θ_* ℚ̄_ℓ`. -/
def adicConstantTransportIso :
    adicConstant k₀' l X' ≅ (transport θ r hθ).obj (adicConstant k₀ l X) :=
  IsoAlgebra.isoMk (adicLowerStarUnitIso l θ).symm (by
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, transport_obj_str,
      adicConstant_frobeniusPowIso, transportCommIso_eq]
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom]
    exact adicLowerStarUnitIso_transport θ _ _ _)

lemma adicConstantTransportIso_hom_hom_f :
    (adicConstantTransportIso (l := l) θ r hθ).hom.hom.f = (adicLowerStarUnitIso l θ).inv :=
  rfl

end Constant

end ProEtaleWeilSheaf

end AlgebraicGeometry
