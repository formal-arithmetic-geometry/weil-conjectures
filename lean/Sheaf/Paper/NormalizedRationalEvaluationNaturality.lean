/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.Paper.DerivedAutomorphismHomEvaluation

/-! # Naturality of normalized rational evaluation

Source: Stacks 08J9; normalized closed data, rationalization step 14
(blueprint: lem-coef-normalized-rational-evaluation-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

private theorem ordinary_evaluation_natural
    {C : Type*} [Category* C] (H : Cᵒᵖ × C ⥤ C)
    (S : CoefficientClosedStructure H) (A A' B B' : C)
    (a : A' ⟶ A) (b : B ⟶ B') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.op b)) (𝟙 A')) ≫
        S.evaluation A' B' =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op A, B))) a) ≫ S.evaluation A B ≫ b := by
  let : MonoidalCategory C := S.monoidal
  have hH : H.map (Prod.mkHom a.op b) =
      H.map (Prod.mkHom a.op (𝟙 B)) ≫ H.map (Prod.mkHom (𝟙 (op A')) b) := by
    rw [← H.map_comp]
    simp
  rw [hH]
  have ht := S.tensor.map_comp
    (Prod.mkHom (H.map (Prod.mkHom a.op (𝟙 B))) (𝟙 A'))
    (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op A')) b)) (𝟙 A'))
  change S.tensor.map (Prod.mkHom
      (H.map (Prod.mkHom a.op (𝟙 B)) ≫ H.map (Prod.mkHom (𝟙 (op A')) b))
      (𝟙 A' ≫ 𝟙 A')) = _ at ht
  rw [Category.id_comp] at ht
  rw [ht, Category.assoc]
  have hb₀ := (S.adjunction A').counit.naturality b
  have hb : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op A')) b)) (𝟙 A')) ≫
    S.evaluation A' B' = S.evaluation A' B ≫ b := by
    simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
      Prod.sectR] using hb₀
  rw [hb, ← Category.assoc]
  simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
    Prod.sectR, Category.assoc] using
      congrArg (fun f ↦ f ≫ b) (S.evaluation_naturality A A' B a)

omit [∀ w : W, Invertible (l : W.residueField w)] in
private theorem completed_unit_natural
    (M M' N N' : DerivedCategory (integralTowerModules l E W))
    (a : M ⟶ M') (b : N ⟶ N') :
    (pullbackTensorCalculus l E W).integralClosed.tensor.map (Prod.mkHom a b) ≫
        podCompletedTensorUnit l E W M' N' =
      podCompletedTensorUnit l E W M N ≫
        (integralCompletedTensor l E W).map (Prod.mkHom a b) := by
  unfold podCompletedTensorUnit
  have h₁ := (pullbackTensorCalculus l E W).adjunction.unit.naturality
    ((pullbackTensorCalculus l E W).integralClosed.tensor.map (Prod.mkHom a b))
  have h₂ := congrArg ((coefficientSequenceLimit l E W).map)
    ((pullbackTensorCalculus l E W).reductionTensor.hom.naturality (Prod.mkHom a b))
  have h₃ := (pullbackTensorIntegralTensorModel l E W).inv.naturality (Prod.mkHom a b)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at h₁ h₂ h₃
  rw [Functor.map_comp, Functor.map_comp] at h₂
  erw [← Category.assoc, h₁, Category.assoc, ← Category.assoc _ _
    ((pullbackTensorIntegralTensorModel l E W).inv.app (M', N')), h₂,
    Category.assoc, h₃]
  simp only [Category.assoc]
  rfl

private theorem integral_transpose_normalization
    (L : sfIntegralConstructibleCategory l E W)
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (f : (constructibleIntegralTensor l E W).obj (L, P.obj.1.unop) ⟶ P.obj.2) :
    ((podIntegralClosed l E W).transpose L P f).hom =
      (pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
        P.obj.2.obj (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ f.hom) := by
  exact eq_of_heq ((podIntegralClosed_existsUnique l E W).exists.choose_spec L P f)

private theorem integral_evaluation_normalization
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) :
    podCompletedTensorUnit l E W ((constructibleIntegralHom l E W).obj P).obj
        P.obj.1.unop.obj ≫ ((podIntegralClosed l E W).evaluation P).hom =
      (pullbackTensorCalculus l E W).integralClosed.evaluation
        P.obj.1.unop.obj P.obj.2.obj := by
  apply (pullbackTensorCalculus l E W).integralClosed.transpose _ _ _ |>.injective
  rw [← integral_transpose_normalization]
  simp only [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply]
  dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation]
  rw [← Adjunction.homEquiv_symm_id]
  exact ((Equiv.apply_symm_apply _ _).symm)

private theorem integral_evaluation_natural
    (P Q : (constructibleIntegralHomPairs l E W).FullSubcategory) (g : P ⟶ Q) :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom ((constructibleIntegralHom l E W).map g) (𝟙 Q.obj.1.unop)) ≫
      (podIntegralClosed l E W).evaluation Q =
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom (𝟙 ((constructibleIntegralHom l E W).obj P)) g.hom.1.unop) ≫
      (podIntegralClosed l E W).evaluation P ≫ g.hom.2 := by
  apply ((podIntegralClosed l E W).transpose _ Q).injective
  apply ObjectProperty.hom_ext
  rw [integral_transpose_normalization, integral_transpose_normalization]
  apply (pullbackTensorCalculus l E W).integralClosed.transpose _ _ _ |>.congr_arg
  change podCompletedTensorUnit l E W _ _ ≫
        ((integralCompletedTensor l E W).map
          (Prod.mkHom (((constructibleIntegralHom l E W).map g).hom) (𝟙 _)) ≫
            ((podIntegralClosed l E W).evaluation Q).hom) =
    podCompletedTensorUnit l E W _ _ ≫
        ((integralCompletedTensor l E W).map
          (Prod.mkHom (𝟙 _) g.hom.1.unop.hom) ≫
            ((podIntegralClosed l E W).evaluation P).hom ≫ g.hom.2.hom)
  erw [← Category.assoc, ← completed_unit_natural, Category.assoc,
    integral_evaluation_normalization]
  erw [← Category.assoc, ← Category.assoc, ← completed_unit_natural,
    Category.assoc]
  simp only [Category.assoc]
  erw [← Category.assoc (podCompletedTensorUnit l E W _ _) _ g.hom.2.hom,
    integral_evaluation_normalization]
  exact ordinary_evaluation_natural _ (pullbackTensorCalculus l E W).integralClosed
    _ _ _ _ g.hom.1.unop.hom g.hom.2.hom

private theorem localized_evaluation
    {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
    (p : R) (T : C × C ⥤ C) (A B I : C)
    (X Z Y : ScalarLocalization R C p) (hX : X = ⟨I⟩)
    (ei : ∀ L : C, (T.obj (L, A) ⟶ B) ≃+ (L ⟶ I))
    (e : (Z ⟶ Y) ≃+ (X ⟶ X))
    (hn : ∀ (f : X.obj ⟶ I) (a : Localization.Away p) (q : X ⟶ X),
      HEq q (a ⊗ₜ[R] f) → HEq (e.symm q) (a ⊗ₜ[R] (ei X.obj).symm f)) :
    HEq (e.symm (𝟙 X)) ((1 : Localization.Away p) ⊗ₜ[R] (ei I).symm (𝟙 I)) := by
  subst X
  exact hn (𝟙 I) 1 (𝟙 _) (HEq.rfl)

private theorem rational_evaluation_normalization
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    HEq ((podRationalClosed l E W).evaluation P)
      ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l E))
        ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (podIntegralClosed l E W).evaluation (integralPairOfRationalHomPair l E W P)) := by
  exact localized_evaluation _ (constructibleIntegralTensor l E W)
    P.obj.1.unop.obj P.obj.2.obj
    ((constructibleIntegralHom l E W).obj (integralPairOfRationalHomPair l E W P))
    _ _ _ ((rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec.1 P)
    (fun L ↦ (podIntegralClosed l E W).transpose L (integralPairOfRationalHomPair l E W P))
    ((podRationalClosed l E W).transpose _ P)
    ((podRationalClosed_existsUnique l E W).exists.choose_spec _ P)

private theorem localized_bilinear_heq
    {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
    (p : R) (T : C × C ⥤ C)
    (M M' N N' Z Z' : ScalarLocalization R C p)
    (U U' V V' : C) (hM : M = ⟨U⟩) (hM' : M' = ⟨U'⟩)
    (hN : N = ⟨V⟩) (hN' : N' = ⟨V'⟩)
    (b : (M ⟶ M') →ₗ[Localization.Away p]
      (N ⟶ N') →ₗ[Localization.Away p] (Z ⟶ Z'))
    (hp : ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj)
      (a c : Localization.Away p),
      HEq (b (a ⊗ₜ[R] f) (c ⊗ₜ[R] g))
        ((a * c) ⊗ₜ[R] T.map (Prod.mkHom f g)))
    (f : M ⟶ M') (g : N ⟶ N') (fi : U ⟶ U') (gi : V ⟶ V')
    (a c : Localization.Away p)
    (hf : HEq f (a ⊗ₜ[R] fi)) (hg : HEq g (c ⊗ₜ[R] gi)) :
    HEq (b f g) ((a * c) ⊗ₜ[R] T.map (Prod.mkHom fi gi)) := by
  subst M M' N N'
  cases hf
  cases hg
  exact hp fi gi a c

private theorem localized_identity_heq
    {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
    (p : R) (X : ScalarLocalization R C p) (I : C) (h : X = ⟨I⟩) :
    HEq (𝟙 X) ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 I) := by
  subst X
  rfl

private theorem localized_evaluation_natural
    {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
    (p : R) (T : C × C ⥤ C)
    (F : ScalarLocalization R C p × ScalarLocalization R C p ⥤ ScalarLocalization R C p)
    (ho : ∀ MN, F.obj MN = ⟨T.obj (MN.1.obj, MN.2.obj)⟩)
    (hm : ∀ M M' N N', ∃ b : (M ⟶ M') →ₗ[Localization.Away p]
        (N ⟶ N') →ₗ[Localization.Away p] (F.obj (M, N) ⟶ F.obj (M', N')),
      (∀ f g, F.map (Prod.mkHom f g) = b f g) ∧
      ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (a c : Localization.Away p),
        HEq (b (a ⊗ₜ[R] f) (c ⊗ₜ[R] g))
          ((a * c) ⊗ₜ[R] T.map (Prod.mkHom f g)))
    (A A' B B' HP HQ : ScalarLocalization R C p) (IP IQ : C)
    (hHP : HP = ⟨IP⟩) (hHQ : HQ = ⟨IQ⟩)
    (evPi : T.obj (IP, A.obj) ⟶ B.obj) (evQi : T.obj (IQ, A'.obj) ⟶ B'.obj)
    (evP : F.obj (HP, A) ⟶ B) (evQ : F.obj (HQ, A') ⟶ B')
    (heP : HEq evP ((1 : Localization.Away p) ⊗ₜ[R] evPi))
    (heQ : HEq evQ ((1 : Localization.Away p) ⊗ₜ[R] evQi))
    (ih : (A'.obj ⟶ A.obj) → (B.obj ⟶ B'.obj) → (IP ⟶ IQ))
    (bh : (A' ⟶ A) →ₗ[Localization.Away p]
      (B ⟶ B') →ₗ[Localization.Away p] (HP ⟶ HQ))
    (ph : ∀ (f : A'.obj ⟶ A.obj) (k : B.obj ⟶ B'.obj) (a c : Localization.Away p),
      HEq (bh (a ⊗ₜ[R] f) (c ⊗ₜ[R] k)) ((a * c) ⊗ₜ[R] ih f k))
    (hn : ∀ (f : A'.obj ⟶ A.obj) (k : B.obj ⟶ B'.obj),
      T.map (Prod.mkHom (ih f k) (𝟙 A'.obj)) ≫ evQi =
        T.map (Prod.mkHom (𝟙 IP) f) ≫ evPi ≫ k)
    (f : A' ⟶ A) (k : B ⟶ B') :
    F.map (Prod.mkHom (bh f k) (𝟙 A')) ≫ evQ =
      F.map (Prod.mkHom (𝟙 HP) f) ≫ evP ≫ k := by
  obtain ⟨bt, et, pt⟩ := hm HP HQ A' A'
  obtain ⟨bu, eu, pu⟩ := hm HP HP A' A
  rw [et, eu]
  have hsource : F.obj (HP, A') = ⟨T.obj (IP, A'.obj)⟩ := by
    rw [ho, hHP]
  have htarget : F.obj (HQ, A') = ⟨T.obj (IQ, A'.obj)⟩ := by
    rw [ho, hHQ]
  have hmid : F.obj (HP, A) = ⟨T.obj (IP, A.obj)⟩ := by
    rw [ho, hHP]
  have hpure (a c : Localization.Away p)
      (f : A'.obj ⟶ A.obj) (k : B.obj ⟶ B'.obj) :
      bt (bh (a ⊗ₜ[R] f) (c ⊗ₜ[R] k)) (𝟙 A') ≫ evQ =
        bu (𝟙 HP) (a ⊗ₜ[R] f) ≫ evP ≫ (c ⊗ₜ[R] k) := by
    have hleft := localized_bilinear_heq p T _ _ _ _ _ _ _ _ _ _
      hHP hHQ rfl rfl bt pt _ _ (ih f k) (𝟙 _) (a * c) 1
      (ph f k a c) (HEq.rfl)
    have hright := localized_bilinear_heq p T _ _ _ _ _ _ _ _ _ _
      hHP hHP rfl rfl bu pu _ _ (𝟙 IP) f 1 a
      (localized_identity_heq p _ _ hHP) (HEq.rfl)
    have hl := heq_comp hsource htarget rfl hleft heQ
    have hr₁ := heq_comp hsource hmid rfl hright heP
    have hr := heq_comp hsource rfl rfl hr₁ (HEq.rfl (a := c ⊗ₜ[R] k))
    rw [← Category.assoc]
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change ScalarLocalization.composition R C p _ _ _ (1 ⊗ₜ[R] evQi)
        (((a * c) * 1) ⊗ₜ[R] T.map (Prod.mkHom (ih f k) (𝟙 A'.obj))) =
      ScalarLocalization.composition R C p _ _ _ (c ⊗ₜ[R] k)
        (ScalarLocalization.composition R C p _ _ _ (1 ⊗ₜ[R] evPi)
          ((1 * a) ⊗ₜ[R] T.map (Prod.mkHom (𝟙 IP) f)))
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, mul_comm c a,
      hn, Category.assoc]
  induction f using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, Limits.zero_comp]
  | tmul a f =>
    induction k using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, Limits.zero_comp, Limits.comp_zero]
    | tmul c k => exact hpure a c f k
    | add k k' hk hk' =>
      simp only [map_add, LinearMap.add_apply, Preadditive.add_comp, hk, hk']
      simp only [← Category.assoc]
      exact (Preadditive.comp_add _ _ _
        (bu (𝟙 HP) (a ⊗ₜ[R] f) ≫ evP) k k').symm
  | add f f' hf hf' =>
    simp only [map_add, LinearMap.add_apply, Preadditive.add_comp, hf, hf']

set_option maxHeartbeats 600000 in
-- The specialization checks the normalized object equalities of three chosen functors.
/-- The Hom-first rational counit is natural in the two internal-Hom entries.
Source: Stacks 08J9; pod-derived-automorphism-hom-evaluation, proof step 14.
Proof: normalize the two tensor objects, Hom objects and counits by their
recorded integral object equalities. Inverse transpose on a pure tensor is the
pure tensor of integral inverse transpose, by podRationalClosed_existsUnique.
In particular evaluation is integral evaluation tensor one. For a pair of
pure-tensor arrows a tensor f and b tensor g, the two sides are a*b times the
integral evaluation naturality equation. That equation follows by precomposition
with the actual completion unit from the ambient counit's naturality; the
normalized completed transpose is injective. The operation normalization gives
bilinearity in f and g, so tensor-product induction extends the equation to
arbitrary rational arrows, including sums. Reinsert the object equalities.
This uses neither faithfulness of individual reductions nor absence of torsion.
(blueprint: lem-coef-normalized-rational-evaluation-naturality). -/
theorem normalizedRationalEvaluation_naturality
    (P P' : (constructibleRationalHomPairs l E W).FullSubcategory) (g : P ⟶ P') :
    (rationalDerivedTensor l E W).map
        (Prod.mkHom ((rationalDerivedInternalHom l E W).map g) (𝟙 P'.obj.1.unop)) ≫
      (podRationalClosed l E W).evaluation P' =
    (rationalDerivedTensor l E W).map
        (Prod.mkHom (𝟙 ((rationalDerivedInternalHom l E W).obj P)) g.hom.1.unop) ≫
      (podRationalClosed l E W).evaluation P ≫ g.hom.2 := by
  obtain ⟨bh, eh, ph⟩ :=
    (rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec.2 P P'
  have hg : g = ObjectProperty.homMk (Prod.mkHom g.hom.1.unop.op g.hom.2) := rfl
  rw [hg]
  erw [eh]
  refine localized_evaluation_natural
    (Padic.coefficientExtensionUniformizer l E) (constructibleIntegralTensor l E W)
    (rationalDerivedTensor l E W)
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.2
    P.obj.1.unop P'.obj.1.unop P.obj.2 P'.obj.2
    ((rationalDerivedInternalHom l E W).obj P)
    ((rationalDerivedInternalHom l E W).obj P')
    ((constructibleIntegralHom l E W).obj (integralPairOfRationalHomPair l E W P))
    ((constructibleIntegralHom l E W).obj (integralPairOfRationalHomPair l E W P'))
    ((rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec.1 P)
    ((rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec.1 P')
    ((podIntegralClosed l E W).evaluation (integralPairOfRationalHomPair l E W P))
    ((podIntegralClosed l E W).evaluation (integralPairOfRationalHomPair l E W P'))
    ((podRationalClosed l E W).evaluation P) ((podRationalClosed l E W).evaluation P')
    (rational_evaluation_normalization l E W P)
    (rational_evaluation_normalization l E W P')
    (fun f k ↦ (constructibleIntegralHom l E W).map
      (X := integralPairOfRationalHomPair l E W P)
      (Y := integralPairOfRationalHomPair l E W P')
      (ObjectProperty.homMk (Prod.mkHom f.op k))) bh ph ?_ g.hom.1.unop g.hom.2
  intro f k
  exact integral_evaluation_natural l E W
    (integralPairOfRationalHomPair l E W P) (integralPairOfRationalHomPair l E W P')
    (ObjectProperty.homMk (Prod.mkHom f.op k))

end WeilConjectures
