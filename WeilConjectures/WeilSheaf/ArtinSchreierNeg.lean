/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier

/-!
# The Artin–Schreier sheaf of the inverse character

The reflection `x ↦ -x` of the affine line commutes with the Artin–Schreier map, so it acts on
`AS_* ℚ̄_ℓ`, conjugating the translation `σ_c` into `σ_{-c}`; it therefore carries the
`ψ`-isotypic component `ℒ_ψ` to the `ψ⁻¹`-isotypic component `ℒ_{ψ⁻¹}` (blueprint
`lem-fd-as-characters`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The exchange morphism `(b⁻¹)_* g_* ℚ̄_ℓ ≅ (g ≫ b⁻¹)_* ℚ̄_ℓ = (a⁻¹ ≫ g)_* ℚ̄_ℓ ≅ g_* (a⁻¹)_* ℚ̄_ℓ
≅ g_* ℚ̄_ℓ` attached to automorphisms `a`, `b` with `g ≫ b⁻¹ = a⁻¹ ≫ g`. -/
noncomputable def lowerStarExchangeStr {X Y : Scheme.{u}} (g : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
    (hg : g ≫ b.inv = a.inv ≫ g) :
    (b.inv)_*[WeilCoefficients.{u} l].obj ((g)_*[WeilCoefficients.{u} l].obj
      (adicConstantSheaf l X)) ⟶ (g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X) :=
  ((lowerStarComp _ g b.inv ≪≫ lowerStarCongr _ hg ≪≫
      (lowerStarComp _ a.inv g).symm).app (adicConstantSheaf l X) ≪≫
    (g)_*[WeilCoefficients.{u} l].mapIso (adicConstantSheafLowerStarIso l a.symm)).hom

/-- The action of an automorphism `σ` of `X` over `Y` on `g_* ℚ̄_ℓ,X`, pulling back sections
along `σ`. -/
noncomputable def lowerStarDeckAction {X Y : Scheme.{u}} (g : X ⟶ Y) (σ : X ≅ X)
    (hσ : σ.hom ≫ g = g) :
    (g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X) ⟶
      (g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X) :=
  (g)_*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l σ).inv ≫
    (lowerStarComp _ σ.hom g).hom.app (adicConstantSheaf l X) ≫
    (lowerStarCongr _ hσ).hom.app (adicConstantSheaf l X)

/-- A variant of `AlgebraicGeometry.ProEtale.lowerStar_map_deckAction_comp_lowerStarExchange`:
if `σ ≫ a = a ≫ σ'`, the exchange morphism of `(a, b)` intertwines the actions of `σ` and `σ'`.
-/
lemma lowerStar_map_lowerStarDeckAction_comp_lowerStarExchangeStr {X Y : Scheme.{u}}
    (g : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y) (σ σ' : X ≅ X) (hg : g ≫ b.inv = a.inv ≫ g)
    (hσ : σ.hom ≫ g = g) (hσ' : σ'.hom ≫ g = g) (hσa : σ.hom ≫ a.hom = a.hom ≫ σ'.hom) :
    (b.inv)_*[WeilCoefficients.{u} l].map (lowerStarDeckAction (l := l) g σ hσ) ≫
        lowerStarExchangeStr g a b hg =
      lowerStarExchangeStr g a b hg ≫ lowerStarDeckAction g σ' hσ' := by
  ext V : 3
  simp only [lowerStarExchangeStr, lowerStarDeckAction, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, lowerStar_map_hom_app',
    Quiver.Hom.unop_op, unop_op, lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarCongr_hom_app_hom_app, adicConstantSheafLowerStarIso_inv_hom_app,
    adicConstantSheafLowerStarIso_hom_hom_app, adicConstantSheaf_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj,
        Iso.symm_inv, MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id,
        Category.comp_id, NatIso.ofComponents_inv_app, MorphismProperty.Over.isoMk_inv_left,
        pullback.congrHom_inv, MorphismProperty.Over.pullbackComp_hom_app_left,
        Category.id_comp, Category.assoc, pullbackLeftPullbackSndIso_inv_fst, limit.lift_π,
        PullbackCone.mk_π_app, pullbackLeftPullbackSndIso_hom_fst, limit.lift_π_assoc,
        cospan_left]
      erw [pullbackLeftPullbackSndIso_inv_fst]
      simp only [pullback.lift_fst]
      exact Category.id_comp _
    · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, reassoc_of% hσa, hσ]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, hσa]


/-- Exchange morphisms of commuting pairs of automorphisms commute. -/
lemma lowerStarExchangeStr_comm {X Y : Scheme.{u}} (g : X ⟶ Y) (a b a' b' : _)
    (hg : g ≫ b.inv = a.inv ≫ g) (hg' : g ≫ b'.inv = a'.inv ≫ g)
    (haa' : (a : X ≅ X).inv ≫ (a' : X ≅ X).inv = a'.inv ≫ a.inv)
    (hbb' : (b : Y ≅ Y).inv ≫ (b' : Y ≅ Y).inv = b'.inv ≫ b.inv) :
    (b'.inv)_*[WeilCoefficients.{u} l].map (lowerStarExchangeStr (l := l) g a b hg) ≫
        lowerStarExchangeStr g a' b' hg' =
      ((lowerStarComp _ b.inv b'.inv ≪≫ lowerStarCongr _ hbb' ≪≫
          (lowerStarComp _ b'.inv b.inv).symm).app _).hom ≫
        (b.inv)_*[WeilCoefficients.{u} l].map (lowerStarExchangeStr g a' b' hg') ≫
        lowerStarExchangeStr g a b hg := by
  ext V : 3
  simp only [lowerStarExchangeStr, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, lowerStar_map_hom_app',
    Quiver.Hom.unop_op, unop_op, lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarCongr_hom_app_hom_app, adicConstantSheafLowerStarIso_inv_hom_app,
    adicConstantSheafLowerStarIso_hom_hom_app, adicConstantSheaf_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  trace_state
  sorry

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

open scoped ProEtale

section AffineLine

variable (k₀ : Type u) [Field k₀]

/-- The scaling by `1` of the affine line is the identity. -/
lemma affineLine.smul_one : affineLine.smul k₀ 1 = 𝟙 _ :=
  AffineSpace.hom_ext (by simp [affineLine.smul]) fun _ ↦ by simp [affineLine.smul]

/-- Scaling by `a b` is scaling by `a` followed by scaling by `b`. -/
lemma affineLine.smul_mul (a b : k₀) :
    affineLine.smul k₀ (a * b) = affineLine.smul k₀ a ≫ affineLine.smul k₀ b := by
  refine AffineSpace.hom_ext (by simp [affineLine.smul]) fun _ ↦ ?_
  simp only [affineLine.smul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.smul_appTop_coord, map_mul]
  rw [← CommRingCat.comp_apply (affineLine k₀ ↘ Spec (.of k₀)).appTop, ← Scheme.Hom.comp_appTop,
    AffineSpace.smul_over]
  ring

/-- The scaling by `-1` is an involution. -/
@[reassoc]
lemma affineLine.smul_neg_one_comp_smul_neg_one :
    affineLine.smul k₀ (-1) ≫ affineLine.smul k₀ (-1) = 𝟙 _ := by
  rw [← affineLine.smul_mul, neg_one_mul, neg_neg, affineLine.smul_one]

/-- The scaling `[c]` conjugates translations: `σ_a ≫ [c] = [c] ≫ σ_{c a}`. -/
lemma affineLine.translation_comp_smul (a c : k₀) :
    affineLine.translation k₀ a ≫ affineLine.smul k₀ c =
      affineLine.smul k₀ c ≫ affineLine.translation k₀ (c * a) := by
  refine AffineSpace.hom_ext (by simp [affineLine.translation, affineLine.smul]) fun _ ↦ ?_
  simp only [affineLine.translation, affineLine.smul, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, AffineSpace.smul_appTop_coord, AffineSpace.translation_appTop_coord,
    map_mul, map_add]
  simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.translation_over,
    AffineSpace.smul_over]
  ring

variable [Finite k₀]

/-- The scaling `[c]` commutes with the Artin–Schreier map, as `c ^ q = c`. -/
@[reassoc]
lemma affineLine.smul_comp_artinSchreierMap (c : k₀) :
    affineLine.smul k₀ c ≫ affineLine.artinSchreierMap k₀ =
      affineLine.artinSchreierMap k₀ ≫ affineLine.smul k₀ c := by
  let := Fintype.ofFinite k₀
  refine AffineSpace.hom_ext (by simp [affineLine.smul, affineLine.artinSchreierMap]) fun _ ↦ ?_
  simp only [affineLine.smul, affineLine.artinSchreierMap, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, AffineSpace.smul_appTop_coord,
    AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow, map_mul]
  simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    AffineSpace.artinSchreierMap_over]
  rw [mul_pow, ← map_pow, ← map_pow, FiniteField.pow_card]
  ring

omit [Finite k₀] in
/-- Base change to `k̄` of equal morphisms over `k₀`. -/
lemma affineLine.geometricFiberMap_congr {φ ψ : affineLine k₀ ⟶ affineLine k₀}
    (h : φ = ψ) (hφ : φ ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) = _)
    (hψ : ψ ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) = _) :
    Scheme.Hom.geometricFiberMap φ hφ = Scheme.Hom.geometricFiberMap ψ hψ := by
  subst h
  rfl

/-- The reflection `x ↦ -x` of the geometric affine line, an involution. -/
noncomputable def affineLine.geometricNegIso :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber where
  hom := Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1)) (comp_over _ _)
  inv := Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1)) (comp_over _ _)
  hom_inv_id := by
    rw [← Scheme.Hom.geometricFiberMap_comp,
      affineLine.geometricFiberMap_congr k₀ (affineLine.smul_neg_one_comp_smul_neg_one k₀) _
        (Category.id_comp _), Scheme.Hom.geometricFiberMap_id]
  inv_hom_id := by
    rw [← Scheme.Hom.geometricFiberMap_comp,
      affineLine.geometricFiberMap_congr k₀ (affineLine.smul_neg_one_comp_smul_neg_one k₀) _
        (Category.id_comp _), Scheme.Hom.geometricFiberMap_id]

lemma affineLine.geometricNegIso_inv :
    (affineLine.geometricNegIso k₀).inv = (affineLine.geometricNegIso k₀).hom :=
  rfl

/-- The base change of `AS ≫ [-1] = [-1] ≫ AS`. -/
lemma affineLine.geometricArtinSchreierMap_comp_geometricNegIso :
    affineLine.geometricArtinSchreierMap k₀ ≫ (affineLine.geometricNegIso k₀).inv =
      (affineLine.geometricNegIso k₀).inv ≫ affineLine.geometricArtinSchreierMap k₀ := by
  simp only [affineLine.geometricNegIso, affineLine.geometricArtinSchreierMap]
  rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
  exact affineLine.geometricFiberMap_congr k₀
    (affineLine.smul_comp_artinSchreierMap k₀ (-1)).symm _ _

/-- The base change of `σ_c ≫ [-1] = [-1] ≫ σ_{-c}`. -/
lemma affineLine.geometricTranslationIso_comp_geometricNegIso (c : k₀) :
    (affineLine.geometricTranslationIso k₀ c).hom ≫ (affineLine.geometricNegIso k₀).hom =
      (affineLine.geometricNegIso k₀).hom ≫ (affineLine.geometricTranslationIso k₀ (-c)).hom := by
  simp only [affineLine.geometricNegIso, affineLine.geometricTranslationIso]
  rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
  refine affineLine.geometricFiberMap_congr k₀ ?_ _ _
  rw [affineLine.translation_comp_smul, neg_one_mul]

/-- The reflection of the geometric affine line commutes with the geometric Frobenius. -/
lemma affineLine.geometricNegIso_inv_comp_frobenius_inv :
    (affineLine.geometricNegIso k₀).inv ≫
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv ≫
        (affineLine.geometricNegIso k₀).inv :=
  Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ (comp_over _ _)

end AffineLine

end AlgebraicGeometry

namespace AlgebraicGeometry

open scoped ProEtale

section Neg

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

instance : IsIso (affineLine.smul k₀ (-1)) :=
  ⟨⟨_, affineLine.smul_neg_one_comp_smul_neg_one k₀,
    affineLine.smul_neg_one_comp_smul_neg_one k₀⟩⟩

variable (k₀ l) in
/-- The action of the reflection `x ↦ -x` on `AS_* ℚ̄_ℓ`, as a morphism of sheaves of modules
`[-1]_* ĀS_* ℚ̄_ℓ ≅ (ĀS ≫ [-1])_* ℚ̄_ℓ = ([-1] ≫ ĀS)_* ℚ̄_ℓ ≅ ĀS_* [-1]_* ℚ̄_ℓ ≅ ĀS_* ℚ̄_ℓ`. -/
noncomputable def affineLine.artinSchreierNegModHom :
    ((affineLine.geometricNegIso k₀).inv)_*ᵃ[l].obj ((ĀS)_*ᵃ[l].obj
      (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ⟶
      (ĀS)_*ᵃ[l].obj
        (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  (ProEtale.adicLowerStarComp l ĀS (affineLine.geometricNegIso k₀).inv).hom.app _ ≫
    (ProEtale.adicLowerStarCongr l
      (affineLine.geometricArtinSchreierMap_comp_geometricNegIso k₀)).hom.app _ ≫
    (ProEtale.adicLowerStarComp l (affineLine.geometricNegIso k₀).inv ĀS).inv.app _ ≫
    (ĀS)_*ᵃ[l].map (ProEtale.adicLowerStarUnitIso l (affineLine.geometricNegIso k₀).symm).hom

omit [Fact (ringChar k₀ ≠ l)] in
lemma affineLine.artinSchreierNegModHom_hom :
    (affineLine.artinSchreierNegModHom k₀ l).hom =
      ProEtale.lowerStarExchangeStr ĀS (affineLine.geometricNegIso k₀)
        (affineLine.geometricNegIso k₀)
        (affineLine.geometricArtinSchreierMap_comp_geometricNegIso k₀) :=
  rfl

instance : IsIso (affineLine.artinSchreierNegModHom k₀ l) := by
  unfold affineLine.artinSchreierNegModHom
  infer_instance

end Neg

end AlgebraicGeometry
