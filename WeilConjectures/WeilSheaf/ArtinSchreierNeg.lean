/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierPullback
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.WeilSheaf.UpperStarId
public import WeilConjectures.WeilSheaf.UpperStarExact
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

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
if `a ≫ σ = σ' ≫ a`, the exchange morphism of `(a, b)` intertwines the actions of `σ` and `σ'`.
-/
lemma lowerStar_map_lowerStarDeckAction_comp_lowerStarExchangeStr {X Y : Scheme.{u}}
    (g : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y) (σ σ' : X ≅ X) (hg : g ≫ b.inv = a.inv ≫ g)
    (hσ : σ.hom ≫ g = g) (hσ' : σ'.hom ≫ g = g) (hσa : a.hom ≫ σ.hom = σ'.hom ≫ a.hom) :
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
        MorphismProperty.Over.mk, ← reassoc_of% hσa, hσ]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, hσa]


/-- `AlgebraicGeometry.ProEtale.pullbackLeftPullbackSndIso_inv_fst` with the base change of an
object of the pro-étale site written as such. -/
@[reassoc]
lemma pullbackLeftPullbackSndIso_inv_fst_fst_over {X Y Z : Scheme.{u}} (b : Z ⟶ Y) (V : Y.ProEt)
    (g : X ⟶ Z) :
    (pullbackLeftPullbackSndIso V.hom b g).inv ≫
        pullback.fst ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ b).obj V).hom g ≫
          pullback.fst V.hom b = pullback.fst _ _ :=
  pullbackLeftPullbackSndIso_inv_fst _ _ _

/-- `pullbackLeftPullbackSndIso_hom_fst` with the base change of an object of the pro-étale site
written as such. -/
@[reassoc]
lemma pullbackLeftPullbackSndIso_hom_fst_over {Y Z W : Scheme.{u}} (b : Z ⟶ Y) (V : Y.ProEt)
    (c : W ⟶ Z) :
    (pullbackLeftPullbackSndIso V.hom b c).hom ≫ pullback.fst V.hom (c ≫ b) =
      pullback.fst ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ b).obj V).hom c ≫
        pullback.fst V.hom b :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

/-- A variant of `AlgebraicGeometry.ProEtale.pullbackLeftPullbackSndIso_inv_fst_fst_over` with an
identity morphism. -/
lemma pullbackLeftPullbackSndIso_inv_id_fst_fst_over {X Y Z : Scheme.{u}} (b : Z ⟶ Y)
    (V : Y.ProEt) (g : X ⟶ Z) :
    (pullbackLeftPullbackSndIso V.hom b g).inv ≫
      𝟙 ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ b).obj V)).left ≫
        pullback.fst ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ b).obj V).hom g ≫
          pullback.fst V.hom b = pullback.fst _ _ := by
  erw [Category.id_comp]
  exact pullbackLeftPullbackSndIso_inv_fst _ _ _

/-- `pullback.lift_fst` with the base change of an object of the pro-étale site written as such. -/
@[reassoc]
lemma pullback_lift_fst_over {X Y Z T : Scheme.{u}} (g : X ⟶ Y) (V : Y.ProEt) (a : Z ⟶ X)
    (h : T ⟶ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V).left) (k : T ⟶ Z)
    (w : h ≫ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V).hom = k ≫ a) :
    pullback.lift h k w ≫ pullback.fst (pullback.snd V.hom g) a = h :=
  pullback.lift_fst _ _ _

/-- `pullback.lift_snd` with the base change of an object of the pro-étale site written as such. -/
@[reassoc]
lemma pullback_lift_snd_over {X Y Z T : Scheme.{u}} (g : X ⟶ Y) (V : Y.ProEt) (a : Z ⟶ X)
    (h : T ⟶ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V).left) (k : T ⟶ Z)
    (w : h ≫ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V).hom = k ≫ a) :
    pullback.lift h k w ≫ pullback.snd (pullback.snd V.hom g) a = k :=
  pullback.lift_snd _ _ _

/-- Exchange morphisms of commuting pairs of automorphisms commute. -/
lemma lowerStarExchangeStr_comm {X Y : Scheme.{u}} (g : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
    (a' : X ≅ X) (b' : Y ≅ Y)
    (hg : g ≫ b.inv = a.inv ≫ g) (hg' : g ≫ b'.inv = a'.inv ≫ g)
    (haa' : a.inv ≫ a'.inv = a'.inv ≫ a.inv) (hbb' : b.inv ≫ b'.inv = b'.inv ≫ b.inv) :
    (b'.inv)_*[WeilCoefficients.{u} l].map (lowerStarExchangeStr (l := l) g a b hg) ≫
        lowerStarExchangeStr g a' b' hg' =
      ((lowerStarComp _ b.inv b'.inv ≪≫ lowerStarCongr _ hbb' ≪≫
          (lowerStarComp _ b'.inv b.inv).symm).app _).hom ≫
        (b.inv)_*[WeilCoefficients.{u} l].map (lowerStarExchangeStr g a' b' hg') ≫
        lowerStarExchangeStr g a b hg := by
  ext V : 3
  have e₁ := @lowerStar_map_hom_app' (WeilCoefficients.{u} l) _
  have e₂ := @lowerStar_obj_obj_map' (WeilCoefficients.{u} l) _
  simp only [lowerStarExchangeStr, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, e₁,
    Quiver.Hom.unop_op, unop_op, lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarCongr_hom_app_hom_app, adicConstantSheafLowerStarIso_inv_hom_app,
    adicConstantSheafLowerStarIso_hom_hom_app, adicConstantSheaf_obj_map, e₂]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  have h₁ : a'.hom ≫ a.hom = a.hom ≫ a'.hom := by
    rw [← cancel_epi a'.inv, ← cancel_epi a.inv]
    simp [reassoc_of% haa']
  have h₂ : a'.hom ≫ a.inv = a.inv ≫ a'.hom := by
    calc a'.hom ≫ a.inv = a.inv ≫ (a.hom ≫ a'.hom) ≫ a.inv := by simp
      _ = a.inv ≫ (a'.hom ≫ a.hom) ≫ a.inv := by rw [h₁]
      _ = a.inv ≫ a'.hom := by simp
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.mk]
        simp [-pullbackLeftPullbackSndIso_hom_fst, -pullbackLeftPullbackSndIso_hom_fst_assoc,
          pullbackLeftPullbackSndIso_inv_fst_fst_over_assoc, pullback_lift_fst_over_assoc,
          pullbackLeftPullbackSndIso_inv_id_fst_fst_over,
          pullbackLeftPullbackSndIso_inv_fst_fst_over, pullback_lift_fst_over,
          pullbackLeftPullbackSndIso_hom_fst_over_assoc, pullbackLeftPullbackSndIso_hom_fst_over,
          pullback_lift_snd_over_assoc]
      · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk, hg, reassoc_of% hg, reassoc_of% h₂]
    · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, reassoc_of% h₁]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, h₁]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

open scoped ProEtale

section AffineLine

variable (k₀ : Type u) [Field k₀]

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
/-- The reflection `x ↦ -x` of the geometric affine line, an involution. -/
noncomputable def affineLine.geometricNegIso :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber where
  hom := Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1)) (comp_over _ _)
  inv := Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1)) (comp_over _ _)
  hom_inv_id := by
    rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_id]
    congr 1
    exact affineLine.smul_neg_one_comp_smul_neg_one k₀
  inv_hom_id := by
    rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_id]
    congr 1
    exact affineLine.smul_neg_one_comp_smul_neg_one k₀

omit [Finite k₀] in
lemma affineLine.geometricNegIso_inv :
    (affineLine.geometricNegIso k₀).inv = (affineLine.geometricNegIso k₀).hom :=
  rfl

/-- The base change of `AS ≫ [-1] = [-1] ≫ AS`. -/
lemma affineLine.geometricArtinSchreierMap_comp_geometricNegIso :
    affineLine.geometricArtinSchreierMap k₀ ≫ (affineLine.geometricNegIso k₀).inv =
      (affineLine.geometricNegIso k₀).inv ≫ affineLine.geometricArtinSchreierMap k₀ := by
  simp only [affineLine.geometricNegIso, affineLine.geometricArtinSchreierMap]
  rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
  congr 1
  exact (affineLine.smul_comp_artinSchreierMap k₀ (-1)).symm

omit [Finite k₀] in
/-- The base change of `[-1] ≫ σ_c = σ_{-c} ≫ [-1]`. -/
lemma affineLine.geometricNegIso_comp_geometricTranslationIso (c : k₀) :
    (affineLine.geometricNegIso k₀).hom ≫ (affineLine.geometricTranslationIso k₀ c).hom =
      (affineLine.geometricTranslationIso k₀ (-c)).hom ≫ (affineLine.geometricNegIso k₀).hom := by
  simp only [affineLine.geometricNegIso, affineLine.geometricTranslationIso]
  rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
  congr 1
  rw [affineLine.translation_comp_smul, neg_one_mul, neg_neg]

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

namespace AlgebraicGeometry

open scoped ProEtale

section NegWeil

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

example : QuasiCompact (affineLine.smul k₀ (-1)) := inferInstance
example : QuasiSeparated (affineLine.smul k₀ (-1)) := inferInstance
example : LocallyOfFiniteType (affineLine.smul k₀ (-1)) := inferInstance

omit [Fact (ringChar k₀ ≠ l)] in
lemma affineLine.artinSchreierPushforward_str_hom_hom_eq :
    (WeilSheaf.artinSchreierPushforward k₀ l).obj.obj.str.hom =
      ProEtale.lowerStarExchangeStr ĀS
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) :=
  artinSchreierPushforward_str_hom_hom

variable (k₀ l) in
/-- The action of the reflection `x ↦ -x` on `AS_* ℚ̄_ℓ`, as a morphism of Weil sheaves
`[-1]_* AS_* ℚ̄_ℓ ⟶ AS_* ℚ̄_ℓ`: it commutes with the Weil structures, the reflection being
defined over `k₀`. -/
noncomputable def WeilSheaf.artinSchreierNegHom :
    (WeilSheaf.lowerStar (affineLine.smul k₀ (-1))).obj
        (WeilSheaf.artinSchreierPushforward k₀ l) ⟶ WeilSheaf.artinSchreierPushforward k₀ l :=
  ObjectProperty.homMk (ObjectProperty.homMk ⟨affineLine.artinSchreierNegModHom k₀ l, by
    refine Mod.hom_ext _ _ ?_
    rw [Mod.comp_hom', Mod.comp_hom', ProEtale.adicLowerStar_map_hom,
      affineLine.artinSchreierNegModHom_hom, affineLine.artinSchreierPushforward_str_hom_hom_eq,
      ← Endofunctor.IsoAlgebra.str_hom, WeilSheaf.lowerStar_obj_obj_str, Iso.trans_hom,
      Mod.comp_hom', Functor.mapIso_hom, ProEtale.adicLowerStar_map_hom,
      Endofunctor.IsoAlgebra.str_hom, affineLine.artinSchreierPushforward_str_hom_hom_eq,
      ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso, Iso.app_hom, Iso.trans_hom,
      Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, Mod.comp_hom', Mod.comp_hom',
      ProEtale.adicLowerStarComp_hom_app_hom, ProEtale.adicLowerStarCongr_hom_app_hom,
      Iso.symm_hom, ProEtale.adicLowerStarComp_inv_app_hom]
    have h := ProEtale.lowerStarExchangeStr_comm (l := l) ĀS (affineLine.geometricNegIso k₀)
      (affineLine.geometricNegIso k₀)
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
      (affineLine.geometricArtinSchreierMap_comp_geometricNegIso k₀)
      (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)
      (affineLine.geometricNegIso_inv_comp_frobenius_inv k₀)
      (affineLine.geometricNegIso_inv_comp_frobenius_inv k₀)
    simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Iso.symm_hom,
      Category.assoc] at h ⊢
    exact h⟩)

end NegWeil

end AlgebraicGeometry

namespace CategoryTheory

/-- The images of two endomorphisms conjugate under an isomorphism are isomorphic. -/
theorem nonempty_iso_image_of_comp_eq {C : Type*} [Category* C] [Abelian C] {A B : C}
    (e : A ≅ B) (f : A ⟶ A) (g : B ⟶ B) (h : f ≫ e.hom = e.hom ≫ g) :
    Nonempty (Limits.image f ≅ Limits.image g) := by
  have hg : (e.inv ≫ Limits.factorThruImage f) ≫ (Limits.image.ι f ≫ e.hom) = g := by
    rw [Category.assoc, Limits.image.fac_assoc, h, Iso.inv_hom_id_assoc]
  have : StrongEpi (e.inv ≫ Limits.factorThruImage f) := strongEpi_of_epi _
  exact ⟨Limits.image.isoStrongEpiMono _ _ hg⟩

end CategoryTheory

namespace AlgebraicGeometry

open scoped ProEtale

section NegWeil2

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

/-- Morphisms of Weil sheaves agree if their underlying morphisms of sheaves of modules do. -/
lemma WeilSheaf.hom_ext_of_hom_hom_f {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    {F G : WeilSheaf k₀ l X} {f g : F ⟶ G} (h : f.hom.hom.f = g.hom.hom.f) : f = g :=
  ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext h))

/-- The reflection conjugates the translation `σ_c` into `σ_{-c}`. -/
lemma WeilSheaf.lowerStar_map_artinSchreierTranslationAction_comp_artinSchreierNegHom (c : k₀) :
    (WeilSheaf.lowerStar (affineLine.smul k₀ (-1))).map
        (WeilSheaf.artinSchreierTranslationAction l c) ≫ WeilSheaf.artinSchreierNegHom k₀ l =
      WeilSheaf.artinSchreierNegHom k₀ l ≫ WeilSheaf.artinSchreierTranslationAction l (-c) := by
  refine WeilSheaf.hom_ext_of_hom_hom_f (Mod.hom_ext _ _ ?_)
  exact ProEtale.lowerStar_map_lowerStarDeckAction_comp_lowerStarExchangeStr ĀS
    (affineLine.geometricNegIso k₀) (affineLine.geometricNegIso k₀)
    (affineLine.geometricTranslationIso k₀ c) (affineLine.geometricTranslationIso k₀ (-c))
    (affineLine.geometricArtinSchreierMap_comp_geometricNegIso k₀)
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ (-c))
    (affineLine.geometricNegIso_comp_geometricTranslationIso k₀ c)

/-- The reflection commutes with the multiplication by scalars. -/
lemma WeilSheaf.lowerStar_map_smulEnd_comp_artinSchreierNegHom (b : PadicAlgCl l) :
    (WeilSheaf.lowerStar (affineLine.smul k₀ (-1))).map
        (WeilSheaf.smulEnd b (WeilSheaf.artinSchreierPushforward k₀ l)) ≫
        WeilSheaf.artinSchreierNegHom k₀ l =
      WeilSheaf.artinSchreierNegHom k₀ l ≫
        WeilSheaf.smulEnd b (WeilSheaf.artinSchreierPushforward k₀ l) := by
  refine WeilSheaf.hom_ext_of_hom_hom_f ?_
  exact (congrArg (· ≫ affineLine.artinSchreierNegModHom k₀ l)
    (ProEtale.AdicSheaf.adicLowerStar_map_smul _ _ _)).trans (ProEtale.AdicSheaf.smul_comp _ _)

/-- The reflection carries the projector `e_ψ` to `e_{ψ⁻¹}`. -/
lemma WeilSheaf.lowerStar_map_artinSchreierIdempotent_comp_artinSchreierNegHom
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    (WeilSheaf.lowerStar (affineLine.smul k₀ (-1))).map (WeilSheaf.artinSchreierIdempotent ψ) ≫
        WeilSheaf.artinSchreierNegHom k₀ l =
      WeilSheaf.artinSchreierNegHom k₀ l ≫ WeilSheaf.artinSchreierIdempotent ψ⁻¹ := by
  let := Fintype.ofFinite k₀
  simp only [WeilSheaf.artinSchreierIdempotent, Functor.map_sum, Functor.map_comp,
    Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc,
    WeilSheaf.lowerStar_map_artinSchreierTranslationAction_comp_artinSchreierNegHom,
    reassoc_of% WeilSheaf.lowerStar_map_smulEnd_comp_artinSchreierNegHom]
  refine Fintype.sum_equiv (Equiv.neg k₀) _ _ fun c ↦ ?_
  rw [Equiv.neg_apply, neg_neg, AddChar.inv_apply]

instance : IsIso (WeilSheaf.artinSchreierNegHom k₀ l) := by
  have : IsIso (WeilSheaf.artinSchreierNegHom k₀ l).hom.hom.f :=
    inferInstanceAs (IsIso (affineLine.artinSchreierNegModHom k₀ l))
  exact WeilSheaf.isIso_of_isIso_hom_hom_f _

/-- The pushforward of pro-étale Weil sheaves along equal morphisms. -/
noncomputable def ProEtaleWeilSheaf.lowerStarIsoOfEq {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {φ φ' : X ⟶ Y}
    [φ.IsOver (Spec (CommRingCat.of k₀))] [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') :
    ProEtaleWeilSheaf.lowerStar k₀ l φ ≅ ProEtaleWeilSheaf.lowerStar k₀ l φ' := by
  subst h
  exact Iso.refl _

variable (k₀ l) in
/-- The pushforward along the reflection `x ↦ -x` is an involution. -/
noncomputable def WeilSheaf.lowerStarNegCompIso :
    WeilSheaf.lowerStar (k₀ := k₀) (l := l) (affineLine.smul k₀ (-1)) ⋙
      WeilSheaf.lowerStar (affineLine.smul k₀ (-1)) ≅ 𝟭 _ :=
  ((WeilSheaf.objectProperty k₀ l (affineLine k₀)).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.lowerStarCompIso k₀ l _ _ ≪≫
        ProEtaleWeilSheaf.lowerStarIsoOfEq (affineLine.smul_neg_one_comp_smul_neg_one k₀) ≪≫
        ProEtaleWeilSheaf.lowerStarIdIso k₀ l (affineLine k₀)) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

variable (k₀ l) in
/-- The pullback along the reflection `x ↦ -x` is the pushforward along it, the reflection being
an involution. -/
noncomputable def WeilSheaf.upperStarNegIsoLowerStarNeg :
    WeilSheaf.upperStar (k₀ := k₀) (l := l) (affineLine.smul k₀ (-1)) ≅
      WeilSheaf.lowerStar (affineLine.smul k₀ (-1)) :=
  (WeilSheaf.upperStarLowerStarAdjunction (affineLine.smul k₀ (-1))).leftAdjointUniq
    (Equivalence.mk _ _ (WeilSheaf.lowerStarNegCompIso k₀ l).symm
      (WeilSheaf.lowerStarNegCompIso k₀ l)).toAdjunction

/-- Blueprint `lem-fd-as-characters`: the pullback of `ℒ_ψ` along the reflection `x ↦ -x` is
`ℒ_{ψ⁻¹}`, i.e. `ℒ_{ψ⁻¹} ≅ ℒ_{ψ(-x)}`. -/
theorem nonempty_iso_artinSchreier_inv_one (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (artinSchreier ψ⁻¹ 1 ≅ artinSchreier ψ (-1)) := by
  obtain ⟨i₁⟩ := nonempty_iso_image_of_comp_eq
    ((WeilSheaf.upperStarNegIsoLowerStarNeg k₀ l).app _)
    ((WeilSheaf.upperStar (affineLine.smul k₀ (-1))).map (WeilSheaf.artinSchreierIdempotent ψ))
    _ ((WeilSheaf.upperStarNegIsoLowerStarNeg k₀ l).hom.naturality _)
  obtain ⟨i₂⟩ := nonempty_iso_image_of_comp_eq (asIso (WeilSheaf.artinSchreierNegHom k₀ l)) _ _
    (WeilSheaf.lowerStar_map_artinSchreierIdempotent_comp_artinSchreierNegHom ψ)
  let Φ := WeilSheaf.upperStar (k₀ := k₀) (l := l) (affineLine.smul k₀ (-1))
  exact ⟨(WeilSheaf.upperStarCongrIso (affineLine.smul_one k₀)).app _ ≪≫
    (WeilSheaf.upperStarIdIso _).app _ ≪≫ i₂.symm ≪≫ i₁.symm ≪≫
    (Φ.mapIso (Abelian.imageIsoImage _).symm ≪≫ Abelian.PreservesImage.iso Φ _ ≪≫
      Abelian.imageIsoImage _).symm⟩

end NegWeil2

end AlgebraicGeometry
