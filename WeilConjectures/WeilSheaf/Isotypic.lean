/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TorsorPairing
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Isotypic components of pushforwards along split torsors of Weil sheaves

Let `π : W ⟶ Z` be an étale morphism of `k₀`-schemes and `τ_g`, `g ∈ G`, automorphisms of `W`
over `Z` and over `k₀`, forming a torsor under the finite abelian group `G` which is split by
the `τ_g` (`AlgebraicGeometry.ProEtale.IsTorsorSplit`). The group acts on the pushforward
`P = π_* ℚ̄_ℓ` of the constant pro-étale Weil sheaf by morphisms of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.torsorTranslation`), and for a character `χ` of `G` the
endomorphism `e_χ = |G|⁻¹ ∑_g χ(-g) σ_g` (`AlgebraicGeometry.ProEtaleWeilSheaf.torsorIdempotent`)
projects onto the `χ`-isotypic component.

The main result (`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_iso_ihom_of_isotypic`) is the Weil
version of `AlgebraicGeometry.ProEtale.isIso_torsorPairingCurry`: given morphisms of pro-étale
Weil sheaves `φᵢ : Mᵢ ⟶ P` on which `G` acts through `χ₁`, `χ₂` and `χ₁ χ₂`, whose adjoints
`π^* Mᵢ ⟶ ℚ̄_ℓ` are isomorphisms, the product of functions induces an isomorphism of pro-étale
Weil sheaves `M₁ ≅ [M₂, M₃]`: the Weil structure of `P` is compatible with the product of
functions, being induced by morphisms of schemes over `k₀`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open scoped ProEtale

namespace ProEtale

variable {Z W Z' W' : Scheme.{u}} {π : W ⟶ Z} {G : Type u} [Finite G] {τ : G → (W ≅ W)}
  {hτ : ∀ g, (τ g).hom ≫ π = π}

/-- **Splittings are stable under base change.** If the automorphisms `τ_g` split `π`, then
their base changes `τ'_g` along `q : Z' ⟶ Z` split the base change `π' : W' ⟶ Z'` of `π`. -/
lemma IsTorsorSplit.of_isPullback (hsplit : IsTorsorSplit π τ hτ) {π' : W' ⟶ Z'} {p : W' ⟶ W}
    {q : Z' ⟶ Z} (sq : IsPullback p π' π q) (τ' : G → (W' ≅ W'))
    (hτ' : ∀ g, (τ' g).hom ≫ π' = π') (hp : ∀ g, (τ' g).hom ≫ p = p ≫ (τ g).hom) :
    IsTorsorSplit π' τ' hτ' := by
  have : IsIso (Sigma.desc fun g : G ↦ pullback.lift (f := π) (g := π) (𝟙 W) (τ g).hom
    (by simp [hτ]) : ∐ (fun _ : G ↦ W) ⟶ pullback π π) := hsplit
  have h₁ := FinitaryPreExtensive.isIso_sigmaDesc_lift_comp π (fun g ↦ (τ g).hom) hτ p
  have hP : IsPullback (pullback.fst π' π') (pullback.snd π' π' ≫ p) (p ≫ π) π := by
    have := (IsPullback.of_hasPullback π' π').flip.paste_horiz sq
    rw [← sq.w] at this
    exact this.flip
  suffices IsIso (Sigma.desc (fun g : G ↦ pullback.lift (f := π') (g := π') (𝟙 _) (τ' g).hom
      (by simp [hτ'])) ≫ hP.isoPullback.hom) from IsIso.of_isIso_comp_right _ hP.isoPullback.hom
  convert h₁ using 1
  refine Sigma.hom_ext _ _ fun g ↦ ?_
  simp only [colimit.ι_desc_assoc, colimit.ι_desc, Cofan.mk_ι_app]
  apply pullback.hom_ext
  · simp
  · simp [hp]

end ProEtale

namespace Scheme.Hom

variable {k : Type u} [Field k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)}

/-- The base change `e × 𝟙 : X₀ ×_{Spec k} Spec k̄ ≅ Y₀ ×_{Spec k} Spec k̄` of an isomorphism
`e : X₀ ≅ Y₀` of schemes over `k`. -/
noncomputable def geometricFiberMapIso (e : X₀ ≅ Y₀) (h : e.hom ≫ g = f) :
    f.geometricFiber ≅ g.geometricFiber where
  hom := geometricFiberMap e.hom h
  inv := geometricFiberMap e.inv (by rw [← h, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    rw [← geometricFiberMap_comp]
    simp only [Iso.hom_inv_id]
    exact geometricFiberMap_id
  inv_hom_id := by
    rw [← geometricFiberMap_comp]
    simp only [Iso.inv_hom_id]
    exact geometricFiberMap_id

@[simp]
lemma geometricFiberMapIso_hom (e : X₀ ≅ Y₀) (h : e.hom ≫ g = f) :
    (geometricFiberMapIso e h).hom = geometricFiberMap e.hom h :=
  rfl

end Scheme.Hom


section Weil

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

section Scalar

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Multiplication by a scalar `b ∈ ℚ̄_ℓ`, as an endomorphism of a pro-étale Weil sheaf: the
Frobenius pullback, a pushforward, commutes with it. -/
noncomputable def ProEtaleWeilSheaf.smulEnd (b : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    A ⟶ A :=
  ObjectProperty.homMk ⟨ProEtale.AdicSheaf.smul (ULift.up b) A.carrier, by
    rw [ProEtale.AdicSheaf.adicLowerStar_map_smul, ProEtale.AdicSheaf.smul_comp]⟩

@[simp]
lemma ProEtaleWeilSheaf.smulEnd_hom_f (b : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    (ProEtaleWeilSheaf.smulEnd b A).hom.f = ProEtale.AdicSheaf.smul (ULift.up b) A.carrier :=
  rfl

lemma ProEtaleWeilSheaf.smulEnd_comp (b : PadicAlgCl l) {A B : ProEtaleWeilSheaf k₀ l X}
    (f : A ⟶ B) : ProEtaleWeilSheaf.smulEnd b A ≫ f = f ≫ ProEtaleWeilSheaf.smulEnd b B :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (ProEtale.AdicSheaf.smul_comp _ _))

lemma ProEtaleWeilSheaf.smulEnd_smulEnd (b c : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf.smulEnd b A ≫ ProEtaleWeilSheaf.smulEnd c A =
      ProEtaleWeilSheaf.smulEnd (c * b) A :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (ProEtale.AdicSheaf.smul_smul _ _ _))

lemma ProEtaleWeilSheaf.smulEnd_one (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf.smulEnd 1 A = 𝟙 A :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (ProEtale.AdicSheaf.smul_one _))

lemma ProEtaleWeilSheaf.smulEnd_add (b c : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf.smulEnd (b + c) A =
      ProEtaleWeilSheaf.smulEnd b A + ProEtaleWeilSheaf.smulEnd c A :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (Mod.hom_ext _ _ (by
    change (ULift.up (b + c) : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _ =
      (ULift.up b : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _ +
        (ULift.up c : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _
    rw [← add_smul]
    rfl)))

lemma ProEtaleWeilSheaf.sum_smulEnd {ι : Type*} (s : Finset ι) (b : ι → PadicAlgCl l)
    (A : ProEtaleWeilSheaf k₀ l X) :
    ∑ i ∈ s, ProEtaleWeilSheaf.smulEnd (b i) A = ProEtaleWeilSheaf.smulEnd (∑ i ∈ s, b i) A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (Mod.hom_ext _ _ (by
      change 0 = (ULift.up 0 : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _
      rw [show (ULift.up 0 : ULift.{u + 1} (PadicAlgCl l)) = 0 from rfl, zero_smul])))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, ProEtaleWeilSheaf.smulEnd_add]

end Scalar

section Torsor

lemma _root_.AlgebraicGeometry.Scheme.Hom.geometricFiberMap_congr {k : Type u} [Field k]
    {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)} {g : Y₀ ⟶ Spec (.of k)} {φ ψ : X₀ ⟶ Y₀}
    (e : φ = ψ) (h : φ ≫ g = f) (h' : ψ ≫ g = f) :
    Scheme.Hom.geometricFiberMap φ h = Scheme.Hom.geometricFiberMap ψ h' := by
  subst e
  rfl

lemma ProEtaleWeilSheaf.adicConstant_str_hom_hom (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.adicConstant k₀ l X).str.hom.hom =
      (ProEtale.adicConstantSheafLowerStarIso l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm).hom :=
  rfl

variable {Z W : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [W.Over (Spec (CommRingCat.of k₀))] (π : W ⟶ Z) [π.IsOver (Spec (CommRingCat.of k₀))]
  {G : Type u} (τ : G → (W ≅ W)) [hτk : ∀ g, (τ g).hom.IsOver (Spec (CommRingCat.of k₀))]
  (hτ : ∀ g, (τ g).hom ≫ π = π)

variable (k₀) in
/-- The base change `τ̄_g` of the automorphism `τ_g` to the geometric fibre. -/
noncomputable abbrev geometricTorsorAut (g : G) :
    (W ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅ (W ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  Scheme.Hom.geometricFiberMapIso (τ g) (comp_over (τ g).hom _)

local notation "π̄" => Scheme.Hom.geometricFiberMap π (comp_over π (Spec (CommRingCat.of k₀)))

omit [Finite k₀] in
variable (k₀) in
lemma geometricTorsorAut_comp (hτ : ∀ g, (τ g).hom ≫ π = π) (g : G) :
    (geometricTorsorAut k₀ τ g).hom ≫ π̄ = π̄ := by
  rw [Scheme.Hom.geometricFiberMapIso_hom, ← Scheme.Hom.geometricFiberMap_comp]
  exact Scheme.Hom.geometricFiberMap_congr (hτ g) _ _

variable (k₀ l) in
/-- The pushforward `π_* ℚ̄_ℓ` of the constant pro-étale Weil sheaf. -/
noncomputable abbrev ProEtaleWeilSheaf.torsorPushforward : ProEtaleWeilSheaf k₀ l Z :=
  (ProEtaleWeilSheaf.lowerStar k₀ l π).obj (ProEtaleWeilSheaf.adicConstant k₀ l W)

/-- The Weil structure of the pushforward of a pro-étale Weil sheaf: the exchange of `π̄_*` with
the Frobenius pushforwards followed by `π̄_*` of the Weil structure. -/
lemma ProEtaleWeilSheaf.lowerStar_obj_str (F : ProEtaleWeilSheaf k₀ l W) :
    ((ProEtaleWeilSheaf.lowerStar k₀ l π).obj F).str =
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l π (comp_over π _)).app
          F.carrier ≪≫ (π̄)_*ᵃ[l].mapIso F.str :=
  Endofunctor.IsoAlgebra.mapOfNatIso_obj_str _ F

/-- The Weil structure of `π_* ℚ̄_ℓ`, on underlying sheaves: the exchange of `π̄_*` with the
Frobenius pushforwards followed by `π̄_*` of the Weil structure of `ℚ̄_ℓ`. -/
lemma ProEtaleWeilSheaf.torsorPushforward_str_hom_hom' :
    (ProEtaleWeilSheaf.torsorPushforward k₀ l π).str.hom.hom =
      ((ProEtale.lowerStarComp _ π̄ (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv ≪≫
          ProEtale.lowerStarCongr _
            (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) ≪≫
          (ProEtale.lowerStarComp _
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv π̄).symm).app
          (ProEtaleWeilSheaf.adicConstant k₀ l W).carrier.X ≪≫
        (π̄)_*[WeilCoefficients.{u} l].mapIso
          (ProEtale.adicConstantSheafLowerStarIso l
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm)).hom := by
  rw [ProEtaleWeilSheaf.lowerStar_obj_str, Iso.trans_hom, Mod.comp_hom',
    Functor.mapIso_hom, ProEtale.adicLowerStar_map_hom]
  erw [ProEtaleWeilSheaf.adicConstant_str_hom_hom]
  rw [ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso, Iso.app_hom, Iso.trans_hom,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, NatTrans.comp_app, Mod.comp_hom',
    Mod.comp_hom', ProEtale.adicLowerStarComp_hom_app_hom, ProEtale.adicLowerStarComp_inv_app_hom,
    ProEtale.adicLowerStarCongr_hom_app_hom]
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]

/-- The Weil structure of `π_* ℚ̄_ℓ`, on underlying sheaves. -/
lemma ProEtaleWeilSheaf.torsorPushforward_str_hom_hom :
    (ProEtaleWeilSheaf.torsorPushforward k₀ l π).str.hom.hom =
      ((ProEtale.lowerStarComp _ π̄ (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv ≪≫
          ProEtale.lowerStarCongr _
            (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) ≪≫
          (ProEtale.lowerStarComp _
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv π̄).symm).app
          (ProEtale.adicConstantSheaf l (W ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≪≫
        (π̄)_*[WeilCoefficients.{u} l].mapIso
          (ProEtale.adicConstantSheafLowerStarIso l
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm)).hom :=
  ProEtaleWeilSheaf.torsorPushforward_str_hom_hom' π

/-- The action of `τ_g` on `π_* ℚ̄_ℓ` commutes with its Weil structure: `τ_g` and `π` are
defined over `k₀`, hence commute with the geometric Frobenius. -/
lemma ProEtaleWeilSheaf.torsorTranslation_comm (g : G) :
    (WeilSheaf.frobeniusPullback k₀ l Z).map (ProEtale.torsorTranslation l π̄
        (geometricTorsorAut k₀ τ) (geometricTorsorAut_comp k₀ π τ hτ) g) ≫
        (ProEtaleWeilSheaf.torsorPushforward k₀ l π).obj.str =
      (ProEtaleWeilSheaf.torsorPushforward k₀ l π).obj.str ≫
        ProEtale.torsorTranslation l π̄ (geometricTorsorAut k₀ τ)
          (geometricTorsorAut_comp k₀ π τ hτ) g := by
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', Mod.comp_hom', ProEtale.adicLowerStar_map_hom,
    ProEtale.torsorTranslation_hom, ← Endofunctor.IsoAlgebra.str_hom,
    ProEtaleWeilSheaf.torsorPushforward_str_hom_hom]
  exact ProEtale.lowerStar_map_deckAction_comp_lowerStarExchange l π̄
    (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    (geometricTorsorAut k₀ τ g)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)
    (geometricTorsorAut_comp k₀ π τ hτ g)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius _ (comp_over (τ g).hom _)) _ rfl

/-- The action of `τ_g` on `π_* ℚ̄_ℓ`, pulling back sections along `τ_g`, as an endomorphism of
pro-étale Weil sheaves. -/
noncomputable def ProEtaleWeilSheaf.torsorTranslation (g : G) :
    ProEtaleWeilSheaf.torsorPushforward k₀ l π ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π :=
  ObjectProperty.homMk ⟨ProEtale.torsorTranslation l π̄ (geometricTorsorAut k₀ τ)
    (geometricTorsorAut_comp k₀ π τ hτ) g, ProEtaleWeilSheaf.torsorTranslation_comm π τ hτ g⟩

@[simp]
lemma ProEtaleWeilSheaf.torsorTranslation_hom_f (g : G) :
    (ProEtaleWeilSheaf.torsorTranslation (l := l) π τ hτ g).hom.f =
      ProEtale.torsorTranslation l π̄ (geometricTorsorAut k₀ τ)
        (geometricTorsorAut_comp k₀ π τ hτ) g :=
  rfl

variable [AddCommGroup G] [Finite G]

/-- The projector `e_χ = |G|⁻¹ ∑_g χ(-g) σ_g` of `π_* ℚ̄_ℓ` onto its `χ`-isotypic component. -/
noncomputable def ProEtaleWeilSheaf.torsorIdempotent (χ : AddChar G (PadicAlgCl l)) :
    ProEtaleWeilSheaf.torsorPushforward k₀ l π ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π :=
  letI := Fintype.ofFinite G
  ∑ g : G, ProEtaleWeilSheaf.smulEnd ((Nat.card G : PadicAlgCl l)⁻¹ * χ (-g)) _ ≫
    ProEtaleWeilSheaf.torsorTranslation π τ hτ g

/-- A morphism on which `G` acts through `χ` is fixed by the projector `e_χ`. -/
lemma ProEtaleWeilSheaf.comp_torsorIdempotent (χ : AddChar G (PadicAlgCl l))
    (hG : (Nat.card G : PadicAlgCl l) ≠ 0) {M : ProEtaleWeilSheaf k₀ l Z}
    (φ : M ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π)
    (hφ : ∀ g, φ ≫ ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
      ProEtaleWeilSheaf.smulEnd (χ g) M ≫ φ) :
    φ ≫ ProEtaleWeilSheaf.torsorIdempotent π τ hτ χ = φ := by
  let := Fintype.ofFinite G
  rw [ProEtaleWeilSheaf.torsorIdempotent, Preadditive.comp_sum]
  have (g : G) : φ ≫ ProEtaleWeilSheaf.smulEnd ((Nat.card G : PadicAlgCl l)⁻¹ * χ (-g)) _ ≫
      ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
      ProEtaleWeilSheaf.smulEnd ((Nat.card G : PadicAlgCl l)⁻¹) M ≫ φ := by
    rw [← Category.assoc, ← ProEtaleWeilSheaf.smulEnd_comp, Category.assoc, hφ,
      ← Category.assoc, ProEtaleWeilSheaf.smulEnd_smulEnd, mul_left_comm,
      ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, mul_one]
  simp_rw [this]
  rw [← Preadditive.sum_comp, ProEtaleWeilSheaf.sum_smulEnd, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_inv_cancel₀ hG,
    ProEtaleWeilSheaf.smulEnd_one, Category.id_comp]

end Torsor

end Weil

end AlgebraicGeometry
