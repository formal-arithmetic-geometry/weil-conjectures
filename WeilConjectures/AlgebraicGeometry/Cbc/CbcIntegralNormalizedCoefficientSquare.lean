/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedCoefficientFamilies
import WeilConjectures.AlgebraicGeometry.Cbc.CbcProperCoefficientSquare
import WeilConjectures.AlgebraicGeometry.Cbc.CbcOpenCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
/-! Integral normalized square, after the proper and open coefficient mates.
Source: coefficient-coherence proof steps 5--10.
(blueprint: lem-cbc-integral-normalized-coefficient-square).
Proof: paste the unit-normalized proper and open coefficient squares, use naturality
of the proper pushforward comparison, then substitute the four beta specifications
and cancel the endpoint conjugations. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard pbcIntegralDatum
  AdicCoefficientDatum.completedPull cbcDerivedOpenShriek

private theorem lifted_map_heq
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Q : A ⥤ B) (F : B ⥤ C) (G : A ⥤ C) (e : Q ⋙ F = G)
    {x y : B} {a b : A} (hx : x = Q.obj a) (hy : y = Q.obj b)
    (f : x ⟶ y) (g : a ⟶ b) (hf : HEq f (Q.map g)) :
    HEq (F.map f) (G.map g) := by
  subst x
  subst y
  rw [eq_of_heq hf]
  exact Functor.hcongr_hom e g

private theorem app_heq
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (t : F ⟶ G) {x y : A} (h : x = y) : HEq (t.app x) (t.app y) := by
  cases h
  rfl

private theorem composite_unit_hom
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C) (S : A ⥤ A) (T : B ⥤ B) (V : C ⥤ C)
    (bF : F ⋙ T ≅ S ⋙ F) (bG : G ⋙ V ≅ T ⋙ G)
    (hS : S = 𝟭 A) (hT : T = 𝟭 B) (hV : V = 𝟭 C)
    (hbF : HEq bF (Iso.refl F)) (hbG : HEq bG (Iso.refl G)) (x : A) :
    HEq (bG.hom.app (F.obj x) ≫ G.map (bF.hom.app x))
      (𝟙 ((F ⋙ G).obj x)) := by
  subst S
  subst T
  subst V
  rw [eq_of_heq hbF, eq_of_heq hbG]
  apply heq_of_eq
  change 𝟙 _ ≫ G.map (𝟙 _) = 𝟙 _
  simp only [Category.id_comp]
  exact G.map_id _

private theorem identity_square
    {A B : Type*} [Category A] [Category B] {U V : A ⥤ B}
    (S : A ⥤ A) (T : B ⥤ B) (bU : U ⋙ T ≅ S ⋙ U) (bV : V ⋙ T ≅ S ⋙ V)
    (hS : S = 𝟭 A) (hT : T = 𝟭 B)
    (hU : ∀ x, HEq (bU.hom.app x) (𝟙 (U.obj x)))
    (hV : ∀ x, HEq (bV.hom.app x) (𝟙 (V.obj x))) (t : U ⟶ V) (x : A) :
    T.map (t.app x) ≫ bV.hom.app x = bU.hom.app x ≫ t.app (S.obj x) := by
  subst S
  subst T
  rw [eq_of_heq (hU x), eq_of_heq (hV x)]
  change t.app x ≫ 𝟙 _ = 𝟙 _ ≫ t.app x
  rw [Category.comp_id, Category.id_comp]

private theorem square_of_inverse_square
    {C : Type*} [Category C] {A B A' B' : C} (i : A ≅ A') (j : B ≅ B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : i.inv ≫ f = g ≫ j.inv) :
    f ≫ j.hom = i.hom ≫ g := by
  apply (cancel_mono j.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

private theorem scalarComparison_eq
    (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    (hd : ∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))
    (hi : ∀ x : T, IsUnit (l : T.presheaf.stalk x))
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (hne : E ≠ F) :
    ∃ e : pbcStageLocalization l Ω T E ⋙ pbcScalarExtension l Ω T hd hi h =
        pbcIntegralScalarExtension l Ω T hd hi h ⋙ pbcStageLocalization l Ω T F,
      pbcScalarIntegralComparison l Ω T hd hi h = eqToIso e := by
  have he := (pbcRationalScalarExtension_exists l Ω T hd hi h).exists.choose_spec
  have hs : pbcScalarExtension l Ω T hd hi h =
      (pbcRationalScalarExtension_exists l Ω T hd hi h).exists.choose := by
    simp only [pbcScalarExtension, dif_neg hne]
  refine ⟨(congrArg (pbcStageLocalization l Ω T E ⋙ ·) hs).trans he, ?_⟩
  have hc := (pbcScalarIntegralComparison_exists l Ω T hd hi h).exists.choose_spec.2 hne
  unfold pbcScalarIntegralComparison
  apply eq_of_heq
  refine hc.trans ?_
  generalize pbcScalarExtension l Ω T hd hi h = B at hs ⊢
  cases hs
  rfl

private theorem ambientSquare
    (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gb c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gb)
    (P : CbcCompletedScalarComparison l Ω g)
    (P' : CbcCompletedScalarComparison l Ω g')
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (r : ℕ) (a : Fin r → PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (ha : Ideal.span (Set.range a) = (pbcStageDatum.{u} l Ω E).ideal)
    (s : ℕ) (b : Fin s → PbcIntegralRing l (pbcFiniteField.{u} l Ω F))
    (hb : Ideal.span (Set.range b) = (pbcStageDatum.{u} l Ω F).ideal)
    (K : pbcAmbientStage l Ω X E)
    (hK : cbcCompleteProperty (pbcStageDatum.{u} l Ω E) X r a ha K)
    (hCK : cbcCompleteProperty (pbcStageDatum.{u} l Ω F) X s b hb
      ((pbcEmbeddingAmbientTensor l _ _ (pbcFiniteFieldInclusion l Ω h) X).obj K)) :
    completedCompactSupportExchange (pbcStageDatum.{u} l Ω F) c c' gb sp sj
        s b hb ⟨_, hCK⟩ ≫
      cbcScalarTargetInverse l _ _ (pbcFiniteFieldInclusion l Ω h) g' c'
        (P'.map h) K =
    cbcScalarSourceInverse l _ _ (pbcFiniteFieldInclusion l Ω h) g c
        (P.map h) K ≫
      (pbcEmbeddingAmbientTensor l _ _ (pbcFiniteFieldInclusion l Ω h) Y').map
        (completedCompactSupportExchange (pbcStageDatum.{u} l Ω E) c c' gb sp sj
          r a ha ⟨K, hK⟩) := by
  let := c.isProper
  let := c.isOpenImmersion
  let := c'.isOpenImmersion
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨Q, hQ⟩ := cbcProperCoefficientSquare l Ω sp P
  have hJ := ((completedOpenExchangeComparison (pbcStageDatum.{u} l Ω E) sj
    r a ha).2 ⟨K, hK⟩).1
  have hp := hQ h ((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E)
    c.i c.isOpenImmersion).obj K)
      (cbcTowerComplete_of_property (pbcStageDatum.{u} l Ω E) c.Z r a ha _ hJ)
  have ho := cbcOpenCoefficientSquare l Ω sj Q P' h r a ha s b hb K hK hCK
  have hn := cbcCompletedExchange_naturality (pbcStageDatum.{u} l Ω F) sp
    ((cbcScalarOpenInverse l _ _ (pbcFiniteFieldInclusion l Ω h) c.i).app K)
  have hd := (pbcScalarDirectImageIso l _ _ (pbcFiniteFieldInclusion l Ω h) c'.g).inv.naturality
    ((cbcDatumCompletedExchange (pbcStageDatum.{u} l Ω E) sj r a ha).app ⟨K, hK⟩)
  dsimp only [Functor.comp_map] at hd
  unfold completedCompactSupportExchange cbcScalarTargetInverse cbcScalarSourceInverse
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [ho]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  erw [hd]
  erw [reassoc_of% hp]
  rfl

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

variable {X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [IsNoetherian X'] [IsNoetherian Y']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]


set_option maxHeartbeats 4000000 in
-- Elaborating the four localized coefficient comparisons exceeds the default limit.
/-- The proper and open coefficient squares paste to the normalized integral beta square.
Source: coefficient-coherence proof steps 5--10.
(blueprint: lem-cbc-integral-normalized-coefficient-square).
Proof: paste the unit-normalized proper and open coefficient squares, use naturality
of the proper pushforward comparison, then substitute the four beta specifications
and cancel the endpoint conjugations. -/
theorem cbcIntegralNormalizedCoefficientSquare
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (H : CbcCompactSupportCoefficientFamily l Ω c)
    (H' : CbcCompactSupportCoefficientFamily l Ω c')
    (P : CbcCompletedPullCoefficientFamily l Ω g)
    (P' : CbcCompletedPullCoefficientFamily l Ω g')
    (τ : ∀ E : Padic.FiniteCoefficientFields l Ω, (H.family.base.Φ E ⋙ P.family.base.Φ E) ⟶
        (P'.family.base.Φ E ⋙ H'.family.base.Φ E))
    (hτ : ∀ E : Padic.FiniteCoefficientFields l Ω,
      ∀ (K : pbcIntegralStage l Ω X E)
    (r : ℕ) (a : Fin r → PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (ha : Ideal.span (Set.range a) = (pbcStageDatum.{u} l Ω E).ideal)
    (hc : cbcCompleteProperty (pbcStageDatum.{u} l Ω E) X r a ha K.obj),
    ∃ (hs : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion ⋙
          (pbcStageDatum.{u} l Ω E).push c.g ⋙
            (pbcStageDatum.{u} l Ω E).completedPull g).obj K.obj))
      (ht : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        (((pbcStageDatum.{u} l Ω E).completedPull g' ⋙
          cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c'.i c'.isOpenImmersion ⋙
            (pbcStageDatum.{u} l Ω E).push c'.g).obj K.obj)),
      HEq ((τ E).app ((pbcStageLocalization l Ω X E).obj K))
        ((pbcStageLocalization l Ω Y' E).map
          (ObjectProperty.homMk (X := ⟨_, hs⟩) (Y := ⟨_, ht⟩)
            (completedCompactSupportExchange (pbcStageDatum.{u} l Ω E)
              c c' gbar properSquare openSquare r a ha ⟨K.obj, hc⟩))))
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcIntegralStage l Ω X E) :
    ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).map
        ((τ E).app ((pbcStageLocalization l Ω X E).obj K)) ≫
      ((P'.family.base.comp H'.family.base).β h).hom.app
        ((pbcStageLocalization l Ω X E).obj K) =
    ((H.family.base.comp P.family.base).β h).hom.app
        ((pbcStageLocalization l Ω X E).obj K) ≫
      (τ F).app (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj
        ((pbcStageLocalization l Ω X E).obj K)) := by
  classical
  by_cases hne : E = F
  · subst F
    have sX := (pbcScalarSystem_units l Ω X dX.out iX.out (le_refl E)).1
    have sY := (pbcScalarSystem_units l Ω Y dY.out iY.out (le_refl E)).1
    have sX' := (pbcScalarSystem_units l Ω X' dX'.out iX'.out (le_refl E)).1
    have sY' := (pbcScalarSystem_units l Ω Y' dY'.out iY'.out (le_refl E)).1
    apply identity_square _ _ ((H.family.base.comp P.family.base).β h)
      ((P'.family.base.comp H'.family.base).β h) sX sY' _ _ (τ E)
    · intro L
      rw [StageSystem.Morphism.comp_β_hom_app]
      exact composite_unit_hom _ _ _ _ _ _ _ sX sY sY' (H.unit E) (P.unit E) L
    · intro L
      rw [StageSystem.Morphism.comp_β_hom_app]
      exact composite_unit_hom _ _ _ _ _ _ _ sX sX' sY' (P'.unit E) (H'.unit E) L
  obtain ⟨eX, heX⟩ := scalarComparison_eq l Ω X dX.out iX.out h hne
  obtain ⟨eY, heY⟩ := scalarComparison_eq l Ω Y dY.out iY.out h hne
  obtain ⟨eX', heX'⟩ := scalarComparison_eq l Ω X' dX'.out iX'.out h hne
  obtain ⟨eY', heY'⟩ := scalarComparison_eq l Ω Y' dY'.out iY'.out h hne
  let IH := fun E : Padic.FiniteCoefficientFields l Ω ↦
    pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion ⋙
        (pbcStageDatum.{u} l Ω E).push c.g) (H.preserves E)
  let IP := fun E : Padic.FiniteCoefficientFields l Ω ↦
    pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      ((pbcStageDatum.{u} l Ω E).completedPull g) (P.preserves E)
  let IH' := fun E : Padic.FiniteCoefficientFields l Ω ↦
    pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c'.i c'.isOpenImmersion ⋙
        (pbcStageDatum.{u} l Ω E).push c'.g) (H'.preserves E)
  let IP' := fun E : Padic.FiniteCoefficientFields l Ω ↦
    pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      ((pbcStageDatum.{u} l Ω E).completedPull g') (P'.preserves E)
  let JX := pbcEmbeddingIntegralTensor l _ _ (pbcFiniteFieldInclusion l Ω h)
    X dX.out iX.out
  let JY := pbcEmbeddingIntegralTensor l _ _ (pbcFiniteFieldInclusion l Ω h)
    Y dY.out iY.out
  let JX' := pbcEmbeddingIntegralTensor l _ _ (pbcFiniteFieldInclusion l Ω h)
    X' dX'.out iX'.out
  let JY' := pbcEmbeddingIntegralTensor l _ _ (pbcFiniteFieldInclusion l Ω h)
    Y' dY'.out iY'.out
  let U := H.family.base.comp P.family.base
  let V := P'.family.base.comp H'.family.base
  have eU (L : Padic.FiniteCoefficientFields l Ω) :
      pbcStageLocalization l Ω X L ⋙ U.Φ L =
        (IH L ⋙ IP L) ⋙ pbcStageLocalization l Ω Y' L := by
    change pbcStageLocalization l Ω X L ⋙
      (H.family.base.Φ L ⋙ P.family.base.Φ L) = _
    rw [← Functor.assoc, H.localization, Functor.assoc, P.localization, ← Functor.assoc]
  have eV (L : Padic.FiniteCoefficientFields l Ω) :
      pbcStageLocalization l Ω X L ⋙ V.Φ L =
        (IP' L ⋙ IH' L) ⋙ pbcStageLocalization l Ω Y' L := by
    change pbcStageLocalization l Ω X L ⋙
      (P'.family.base.Φ L ⋙ H'.family.base.Φ L) = _
    rw [← Functor.assoc, P'.localization, Functor.assoc, H'.localization, ← Functor.assoc]
  have eXc := eX
  have eYc := eY
  have eX'c := eX'
  have eY'c := eY'
  rw [pbcIntegralScalarExtension_eq] at eXc eYc eX'c eY'c
  let aH : (IH F).obj (JX.obj K) ⟶ JY.obj ((IH E).obj K) :=
    ObjectProperty.homMk
      (cbcScalarCompactSupportInverse l _ _ (pbcFiniteFieldInclusion l Ω h) c K.obj)
  let aP : (IP F).obj (JY.obj ((IH E).obj K)) ⟶
      JY'.obj ((IP E).obj ((IH E).obj K)) :=
    ObjectProperty.homMk ((P.comparison h).app ((IH E).obj K).obj)
  let aP' : (IP' F).obj (JX.obj K) ⟶ JX'.obj ((IP' E).obj K) :=
    ObjectProperty.homMk ((P'.comparison h).app K.obj)
  let aH' : (IH' F).obj (JX'.obj ((IP' E).obj K)) ⟶
      JY'.obj ((IH' E).obj ((IP' E).obj K)) :=
    ObjectProperty.homMk
      (cbcScalarCompactSupportInverse l _ _ (pbcFiniteFieldInclusion l Ω h) c'
        ((IP' E).obj K).obj)
  obtain ⟨_, _, bH⟩ := H.beta h K
  obtain ⟨_, _, bP⟩ := P.beta h ((IH E).obj K)
  obtain ⟨_, _, bP'⟩ := P'.beta h K
  obtain ⟨_, _, bH'⟩ := H'.beta h ((IP' E).obj K)
  rw [heX, heY] at bH
  rw [heY, heY'] at bP
  rw [heX, heX'] at bP'
  rw [heX', heY'] at bH'
  simp only [eqToIso.inv, eqToIso.hom, eqToHom_app, eqToHom_map,
    eqToHom_comp_heq_iff] at bH bP bP' bH'
  simp only [← Category.assoc, comp_eqToHom_heq_iff] at bH bP bP' bH'
  change HEq ((H.family.base.β h).inv.app
    ((pbcStageLocalization l Ω X E).obj K))
      ((pbcStageLocalization l Ω Y F).map aH) at bH
  change HEq ((P.family.base.β h).inv.app
    ((pbcStageLocalization l Ω Y E).obj ((IH E).obj K)))
      ((pbcStageLocalization l Ω Y' F).map aP) at bP
  change HEq ((P'.family.base.β h).inv.app
    ((pbcStageLocalization l Ω X E).obj K))
      ((pbcStageLocalization l Ω X' F).map aP') at bP'
  change HEq ((H'.family.base.β h).inv.app
    ((pbcStageLocalization l Ω X' E).obj ((IP' E).obj K)))
      ((pbcStageLocalization l Ω Y' F).map aH') at bH'
  have hHs : (H.family.base.Φ F).obj
        (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj
          ((pbcStageLocalization l Ω X E).obj K)) =
      (pbcStageLocalization l Ω Y F).obj ((IH F).obj (JX.obj K)) := by
    exact (congrArg (H.family.base.Φ F).obj (Functor.congr_obj eXc K)).trans
      (Functor.congr_obj (H.localization F) (JX.obj K))
  have hHt : ((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj
        ((H.family.base.Φ E).obj ((pbcStageLocalization l Ω X E).obj K)) =
      (pbcStageLocalization l Ω Y F).obj (JY.obj ((IH E).obj K)) := by
    exact (congrArg ((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj
      (Functor.congr_obj (H.localization E) K)).trans
      (Functor.congr_obj eYc ((IH E).obj K))
  have hPs : (P'.family.base.Φ F).obj
        (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj
          ((pbcStageLocalization l Ω X E).obj K)) =
      (pbcStageLocalization l Ω X' F).obj ((IP' F).obj (JX.obj K)) := by
    exact (congrArg (P'.family.base.Φ F).obj (Functor.congr_obj eXc K)).trans
      (Functor.congr_obj (P'.localization F) (JX.obj K))
  have hPt : ((pbcScalarSystem l Ω X' dX'.out iX'.out).T h).obj
        ((P'.family.base.Φ E).obj ((pbcStageLocalization l Ω X E).obj K)) =
      (pbcStageLocalization l Ω X' F).obj (JX'.obj ((IP' E).obj K)) := by
    exact (congrArg ((pbcScalarSystem l Ω X' dX'.out iX'.out).T h).obj
      (Functor.congr_obj (P'.localization E) K)).trans
      (Functor.congr_obj eX'c ((IP' E).obj K))
  have hUs : (U.Φ F).obj
        (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj
          ((pbcStageLocalization l Ω X E).obj K)) =
      (pbcStageLocalization l Ω Y' F).obj ((IH F ⋙ IP F).obj (JX.obj K)) := by
    exact (congrArg (U.Φ F).obj (Functor.congr_obj eXc K)).trans
      (Functor.congr_obj (eU F) (JX.obj K))
  have hUt : ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).obj
        ((U.Φ E).obj ((pbcStageLocalization l Ω X E).obj K)) =
      (pbcStageLocalization l Ω Y' F).obj (JY'.obj ((IH E ⋙ IP E).obj K)) := by
    exact (congrArg ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).obj
      (Functor.congr_obj (eU E) K)).trans
      (Functor.congr_obj eY'c ((IH E ⋙ IP E).obj K))
  have hVs : (V.Φ F).obj
        (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj
          ((pbcStageLocalization l Ω X E).obj K)) =
      (pbcStageLocalization l Ω Y' F).obj ((IP' F ⋙ IH' F).obj (JX.obj K)) := by
    exact (congrArg (V.Φ F).obj (Functor.congr_obj eXc K)).trans
      (Functor.congr_obj (eV F) (JX.obj K))
  have hVt : ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).obj
        ((V.Φ E).obj ((pbcStageLocalization l Ω X E).obj K)) =
      (pbcStageLocalization l Ω Y' F).obj (JY'.obj ((IP' E ⋙ IH' E).obj K)) := by
    exact (congrArg ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).obj
      (Functor.congr_obj (eV E) K)).trans
      (Functor.congr_obj eY'c ((IP' E ⋙ IH' E).obj K))
  have mH := lifted_map_heq (pbcStageLocalization l Ω Y F) (P.family.base.Φ F)
    (IP F ⋙ pbcStageLocalization l Ω Y' F) (P.localization F) hHs hHt _ aH bH
  have mP' := lifted_map_heq (pbcStageLocalization l Ω X' F) (H'.family.base.Φ F)
    (IH' F ⋙ pbcStageLocalization l Ω Y' F) (H'.localization F) hPs hPt _ aP' bP'
  have nP := (app_heq (P.family.base.β h).inv
    (Functor.congr_obj (H.localization E) K)).trans bP
  have nH' := (app_heq (H'.family.base.β h).inv
    (Functor.congr_obj (P'.localization E) K)).trans bH'
  have hUm : (P.family.base.Φ F).obj
        (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj
          ((H.family.base.Φ E).obj ((pbcStageLocalization l Ω X E).obj K))) =
      (pbcStageLocalization l Ω Y' F).obj ((IP F).obj (JY.obj ((IH E).obj K))) :=
    (congrArg (P.family.base.Φ F).obj hHt).trans
      (Functor.congr_obj (P.localization F) (JY.obj ((IH E).obj K)))
  have hVm : (H'.family.base.Φ F).obj
        (((pbcScalarSystem l Ω X' dX'.out iX'.out).T h).obj
          ((P'.family.base.Φ E).obj ((pbcStageLocalization l Ω X E).obj K))) =
      (pbcStageLocalization l Ω Y' F).obj ((IH' F).obj (JX'.obj ((IP' E).obj K))) :=
    (congrArg (H'.family.base.Φ F).obj hPt).trans
      (Functor.congr_obj (H'.localization F) (JX'.obj ((IP' E).obj K)))
  let aU := (IP F).map aH ≫ aP
  let aV := (IH' F).map aP' ≫ aH'
  have bU : HEq ((U.β h).inv.app ((pbcStageLocalization l Ω X E).obj K))
      ((pbcStageLocalization l Ω Y' F).map aU) := by
    rw [StageSystem.Morphism.comp_β_inv_app]
    exact (heq_comp hUs hUm hUt mH nP).trans
      (heq_of_eq ((pbcStageLocalization l Ω Y' F).map_comp _ _).symm)
  have bV : HEq ((V.β h).inv.app ((pbcStageLocalization l Ω X E).obj K))
      ((pbcStageLocalization l Ω Y' F).map aV) := by
    rw [StageSystem.Morphism.comp_β_inv_app]
    exact (heq_comp hVs hVm hVt mP' nH').trans
      (heq_of_eq ((pbcStageLocalization l Ω Y' F).map_comp _ _).symm)
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (pbcStageDatum.{u} l Ω E).finitelyGenerated
  obtain ⟨s, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (pbcStageDatum.{u} l Ω F).finitelyGenerated
  have hc := wfConstructible_complete X (pbcStageDatum.{u} l Ω E) r a ha K
  have hcF := wfConstructible_complete X (pbcStageDatum.{u} l Ω F) s b hb (JX.obj K)
  let tE : (IH E ⋙ IP E).obj K ⟶ (IP' E ⋙ IH' E).obj K :=
    ObjectProperty.homMk (completedCompactSupportExchange (pbcStageDatum.{u} l Ω E)
      c c' gbar properSquare openSquare r a ha ⟨K.obj, hc⟩)
  let tF : (IH F ⋙ IP F).obj (JX.obj K) ⟶ (IP' F ⋙ IH' F).obj (JX.obj K) :=
    ObjectProperty.homMk (completedCompactSupportExchange (pbcStageDatum.{u} l Ω F)
      c c' gbar properSquare openSquare s b hb ⟨(JX.obj K).obj, hcF⟩)
  obtain ⟨_, _, tEn⟩ := hτ E K r a ha hc
  obtain ⟨_, _, tFn⟩ := hτ F (JX.obj K) s b hb hcF
  change HEq ((τ E).app ((pbcStageLocalization l Ω X E).obj K))
    ((pbcStageLocalization l Ω Y' E).map tE) at tEn
  change HEq ((τ F).app ((pbcStageLocalization l Ω X F).obj (JX.obj K)))
    ((pbcStageLocalization l Ω Y' F).map tF) at tFn
  have mtE := lifted_map_heq (pbcStageLocalization l Ω Y' E)
    ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h)
    (JY' ⋙ pbcStageLocalization l Ω Y' F) eY'c
    (Functor.congr_obj (eU E) K) (Functor.congr_obj (eV E) K) _ tE tEn
  have ntF := (app_heq (τ F) (Functor.congr_obj eXc K)).trans tFn
  have ambient : tF ≫ aV = aU ≫ JY'.map tE := by
    apply ObjectProperty.hom_ext
    dsimp [tF, tE, aU, aV, aH, aP, aP', aH', IH, IH', IP, IP',
      JX, JY, JX', JY', pbcConditionalIntegral, pbcEmbeddingIntegralTensor]
    simpa only [cbcScalarSourceInverse, cbcScalarTargetInverse,
      cbcScalarCompactSupportInverse, cbcScalarOpenInverse, cbcScalarOrdinaryIso,
      Functor.map_comp, Category.assoc] using
      (ambientSquare l Ω c c' gbar properSquare openSquare
        ⟨P.comparison, P.completionUnit⟩ ⟨P'.comparison, P'.completionUnit⟩
        h r a ha s b hb K.obj hc hcF)
  have hleft := heq_comp hUs hUt hVt bU mtE
  have hright := heq_comp hUs hVs hVt ntF bV
  have hinv : (U.β h).inv.app ((pbcStageLocalization l Ω X E).obj K) ≫
      ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).map
        ((τ E).app ((pbcStageLocalization l Ω X E).obj K)) =
    (τ F).app (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj
      ((pbcStageLocalization l Ω X E).obj K)) ≫
        (V.β h).inv.app ((pbcStageLocalization l Ω X E).obj K) := by
    apply eq_of_heq
    refine hleft.trans ((heq_of_eq ?_).trans hright.symm)
    change (pbcStageLocalization l Ω Y' F).map aU ≫
        (pbcStageLocalization l Ω Y' F).map (JY'.map tE) =
      (pbcStageLocalization l Ω Y' F).map tF ≫
        (pbcStageLocalization l Ω Y' F).map aV
    simpa only [Functor.map_comp] using
      congrArg (pbcStageLocalization l Ω Y' F).map ambient.symm
  exact square_of_inverse_square ((U.β h).app ((pbcStageLocalization l Ω X E).obj K))
    ((V.β h).app ((pbcStageLocalization l Ω X E).obj K)) _ _ hinv

end AlgebraicGeometry.Scheme
