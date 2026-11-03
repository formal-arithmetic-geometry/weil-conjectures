/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation

/-! # Naturality of normalized rational evaluation

Source: Stacks 08J9; normalized closed data, rationalization step 14
(blueprint: lem-coef-normalized-rational-evaluation-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard

private theorem ambientEvaluation_naturality
    {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P Q P' Q' : D)
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
        S.evaluation P' Q' =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q ≫ g := by
  let := S.monoidal
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      S.evaluation P' Q = S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' Q f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P')) ≫
      S.evaluation P' Q' = S.evaluation P' Q ≫ g := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      (S.adjunction P').counit.naturality g
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') := by
    ext <;> simp
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, he]
  exact Category.assoc _ _ _

private theorem ambientInverseTranspose_naturality
    {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (L L' P Q P' Q' : D)
    (f : L' ⟶ L) (g : P' ⟶ P) (h : Q ⟶ Q') (phi : L ⟶ H.obj (op P, Q)) :
    (S.transpose L' P' Q').symm (f ≫ phi ≫ H.map (Prod.mkHom g.op h)) =
      S.tensor.map (Prod.mkHom f g) ≫ (S.transpose L P Q).symm phi ≫ h := by
  let := S.monoidal
  have he (T P Q : D) (psi : T ⟶ H.obj (op P, Q)) :
      (S.transpose T P Q).symm psi =
        S.tensor.map (Prod.mkHom psi (𝟙 P)) ≫ S.evaluation P Q :=
    by
      have ht : S.tensor.map (Prod.mkHom psi (𝟙 P)) =
          (@MonoidalCategory.tensorRight D _ S.monoidal P).map psi :=
        @MonoidalCategory.tensorHom_id D _ S.monoidal T _ psi P
      rw [ht]
      exact (S.adjunction P).homEquiv_counit (g := psi)
  rw [he, he, Category.assoc]
  have hn := S.tensor.map (Prod.mkHom (f ≫ phi) (𝟙 P')) ≫=
    ambientEvaluation_naturality S P Q P' Q' g h
  simpa only [← Functor.map_comp_assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
    Category.comp_id, Category.id_comp, Category.assoc] using hn

private def completedTensorUnitNat
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :
    (pullbackTensorCalculus l E W).integralClosed.tensor ⟶ integralCompletedTensor l E W :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (pullbackTensorCalculus l E W).adjunction.unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (pullbackTensorCalculus l E W).reductionTensor.hom
      (coefficientSequenceLimit l E W) ≫
    (pullbackTensorIntegralTensorModel l E W).inv

private theorem completedTensorUnit_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (M N M' N' : DerivedCategory (integralTowerModules l E W))
    (f : M ⟶ M') (g : N ⟶ N') :
    (pullbackTensorCalculus l E W).integralClosed.tensor.map (Prod.mkHom f g) ≫
        podCompletedTensorUnit l E W M' N' =
      podCompletedTensorUnit l E W M N ≫
        (integralCompletedTensor l E W).map (Prod.mkHom f g) := by
  let := (pullbackTensorCalculus l E W).integralClosed.monoidal
  simpa [completedTensorUnitNat, podCompletedTensorUnit,
    CoefficientClosedStructure.tensor, Category.assoc] using
    (completedTensorUnitNat l E W).naturality (Prod.mkHom f g)

private theorem integralTranspose_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (L : sfIntegralConstructibleCategory l E W)
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (f : (constructibleIntegralTensor l E W).obj (L, P.obj.1.unop) ⟶ P.obj.2) :
    ((podIntegralClosed l E W).transpose L P f).hom =
      (pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
        P.obj.2.obj (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ f.hom) := by
  exact eq_of_heq ((podIntegralClosed_existsUnique l E W).exists.choose_spec L P f)

private theorem integralInverseTranspose_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (L : sfIntegralConstructibleCategory l E W)
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (phi : L ⟶ (constructibleIntegralHom l E W).obj P) :
    podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫
        (((podIntegralClosed l E W).transpose L P).symm phi).hom =
      ((pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
        P.obj.2.obj).symm phi.hom := by
  apply ((pullbackTensorCalculus l E W).integralClosed.transpose _ _ _).injective
  rw [← integralTranspose_normalization, AddEquiv.apply_symm_apply,
    Equiv.apply_symm_apply]

private theorem integralInverseTranspose_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (L L' : sfIntegralConstructibleCategory l E W)
    (P P' : (constructibleIntegralHomPairs l E W).FullSubcategory) (f : L' ⟶ L)
    (g : P ⟶ P') (phi : L ⟶ (constructibleIntegralHom l E W).obj P) :
    ((podIntegralClosed l E W).transpose L' P').symm
        (f ≫ phi ≫ (constructibleIntegralHom l E W).map g) =
      (constructibleIntegralTensor l E W).map (Prod.mkHom f g.hom.1.unop) ≫
        ((podIntegralClosed l E W).transpose L P).symm phi ≫ g.hom.2 := by
  have h := ambientInverseTranspose_naturality
    (pullbackTensorCalculus l E W).integralClosed L.obj L'.obj
      P.obj.1.unop.obj P.obj.2.obj P'.obj.1.unop.obj P'.obj.2.obj
      f.hom g.hom.1.unop.hom g.hom.2.hom phi.hom
  apply ((podIntegralClosed l E W).transpose L' P').injective
  apply ObjectProperty.hom_ext
  rw [integralTranspose_normalization, integralTranspose_normalization]
  change _ = (pullbackTensorCalculus l E W).integralClosed.transpose _ _ _
    (podCompletedTensorUnit l E W _ _ ≫
      ((integralCompletedTensor l E W).map (Prod.mkHom f.hom g.hom.1.unop.hom) ≫
        (((podIntegralClosed l E W).transpose L P).symm phi).hom ≫ g.hom.2.hom))
  have hu := integralInverseTranspose_normalization l E W L P phi
  have hn := completedTensorUnit_naturality l E W L'.obj P'.obj.1.unop.obj
    L.obj P.obj.1.unop.obj f.hom g.hom.1.unop.hom
  have heq : podCompletedTensorUnit l E W L'.obj P'.obj.1.unop.obj ≫
      (integralCompletedTensor l E W).map (Prod.mkHom f.hom g.hom.1.unop.hom) ≫
      (((podIntegralClosed l E W).transpose L P).symm phi).hom ≫ g.hom.2.hom =
      (pullbackTensorCalculus l E W).integralClosed.tensor.map
        (Prod.mkHom f.hom g.hom.1.unop.hom) ≫
      ((pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
        P.obj.2.obj).symm phi.hom ≫ g.hom.2.hom := by
    calc
      _ = (pullbackTensorCalculus l E W).integralClosed.tensor.map
          (Prod.mkHom f.hom g.hom.1.unop.hom) ≫
          (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫
          (((podIntegralClosed l E W).transpose L P).symm phi).hom) ≫ g.hom.2.hom := by
            simpa only [Category.assoc] using
              congrArg (fun k ↦ k ≫
                (((podIntegralClosed l E W).transpose L P).symm phi).hom ≫ g.hom.2.hom)
                  hn.symm
      _ = _ := by rw [hu]
  exact congrArg ((pullbackTensorCalculus l E W).integralClosed.transpose
    L'.obj P'.obj.1.unop.obj P'.obj.2.obj)
      ((integralInverseTranspose_normalization l E W L' P'
        (f ≫ phi ≫ (constructibleIntegralHom l E W).map g)).trans (h.trans heq.symm))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

private theorem integralEvaluation_naturality
    (P P' : (constructibleIntegralHomPairs l E W).FullSubcategory) (g : P ⟶ P') :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom ((constructibleIntegralHom l E W).map g) (𝟙 P'.obj.1.unop)) ≫
      (podIntegralClosed l E W).evaluation P' =
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom (𝟙 ((constructibleIntegralHom l E W).obj P)) g.hom.1.unop) ≫
      (podIntegralClosed l E W).evaluation P ≫ g.hom.2 := by
  have h := integralInverseTranspose_naturality l E W
    ((constructibleIntegralHom l E W).obj P) ((constructibleIntegralHom l E W).obj P)
    P P' (𝟙 _) g (𝟙 _)
  simp only [Category.id_comp] at h
  dsimp only [PodPartialClosed.evaluation]
  rw [h.symm]
  apply ((podIntegralClosed l E W).transpose _ P').injective
  rw [(podIntegralClosed l E W).parameter_naturality]
  simp only [AddEquiv.apply_symm_apply, Category.comp_id]

private theorem tensorMap_heq
    {R : Type*} [CommRing R] {A : Type*} [Category* A] [Preadditive A] [Linear R A]
    (p : R) (T : A × A ⥤ A)
    (F : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (hm : ∀ M M' N N', ∃ b : (M ⟶ M') →ₗ[Localization.Away p]
        (N ⟶ N') →ₗ[Localization.Away p] (F.obj (M, N) ⟶ F.obj (M', N')),
      (∀ f g, F.map (Prod.mkHom f g) = b f g) ∧
      ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (a b' : Localization.Away p),
        HEq (b (a ⊗ₜ[R] f) (b' ⊗ₜ[R] g))
          ((a * b') ⊗ₜ[R] T.map (Prod.mkHom f g)))
    {M M' N N' : ScalarLocalization R A p} {X X' Y Y' : A}
    (hM : M = ⟨X⟩) (hM' : M' = ⟨X'⟩) (hN : N = ⟨Y⟩) (hN' : N' = ⟨Y'⟩)
    {f : M ⟶ M'} {g : N ⟶ N'} (f₀ : X ⟶ X') (g₀ : Y ⟶ Y')
    (a b : Localization.Away p) (hf : HEq f (a ⊗ₜ[R] f₀))
    (hg : HEq g (b ⊗ₜ[R] g₀)) :
    HEq (F.map (Prod.mkHom f g)) ((a * b) ⊗ₜ[R] T.map (Prod.mkHom f₀ g₀)) := by
  cases hM
  cases hM'
  cases hN
  cases hN'
  cases hf
  cases hg
  obtain ⟨b, he, hp⟩ := hm _ _ _ _
  rw [he]
  exact hp _ _ _ _

private theorem localizedEvaluation_heq
    {R : Type*} [CommRing R] {A : Type*} [Category* A] [Preadditive A] [Linear R A]
    (p : R) (T : A × A ⥤ A)
    (F : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (M N X : ScalarLocalization R A p) (X₀ : A)
    (e : ∀ L, (F.obj (L, M) ⟶ N) ≃+ (L ⟶ X))
    (e₀ : ∀ L, (T.obj (L, M.obj) ⟶ N.obj) ≃+ (L ⟶ X₀))
    (hX : X = ⟨X₀⟩)
    (hn : ∀ L (f : L.obj ⟶ X₀) (a : Localization.Away p) (q : L ⟶ X),
      HEq q (a ⊗ₜ[R] f) → HEq ((e L).symm q) (a ⊗ₜ[R] (e₀ L.obj).symm f)) :
    HEq ((e X).symm (𝟙 _)) ((1 : Localization.Away p) ⊗ₜ[R] (e₀ X₀).symm (𝟙 _)) := by
  cases hX
  exact hn _ (𝟙 _) 1 (𝟙 _) HEq.rfl

private theorem rationalEvaluation_normalization
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    HEq ((podRationalClosed l E W).evaluation P)
      ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l E))
        ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (podIntegralClosed l E W).evaluation (integralPairOfRationalHomPair l E W P)) := by
  exact localizedEvaluation_heq _ (constructibleIntegralTensor l E W)
    (rationalDerivedTensor l E W) P.obj.1.unop P.obj.2
    ((rationalDerivedInternalHom l E W).obj P) _
    (fun L ↦ (podRationalClosed l E W).transpose L P)
    (fun L ↦ (podIntegralClosed l E W).transpose L (integralPairOfRationalHomPair l E W P))
    ((rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec.1 P)
    (fun L f a q h ↦ (podRationalClosed_existsUnique l E W).exists.choose_spec L P f a q h)

attribute [local irreducible] constructibleIntegralHom constructibleIntegralTensor
  integralDerivedInternalHom pullbackTensorCalculus podIntegralClosed

private def localizedPairs {R : Type*} [CommRing R] {A : Type*} [Category* A]
    [Preadditive A] [Linear R A] (p : R) (J : ObjectProperty (Aᵒᵖ × A)) :
    ObjectProperty ((ScalarLocalization R A p)ᵒᵖ × ScalarLocalization R A p) :=
  fun P ↦ J (op P.1.unop.obj, P.2.obj)

private def underlyingPair {R : Type*} [CommRing R] {A : Type*} [Category* A]
    [Preadditive A] [Linear R A] (p : R) (J : ObjectProperty (Aᵒᵖ × A))
    (P : (localizedPairs p J).FullSubcategory) : J.FullSubcategory :=
  ⟨(op P.obj.1.unop.obj, P.obj.2.obj), P.property⟩

private theorem localizedEvaluation_naturality
    {R : Type*} [CommRing R] {A : Type*} [Category* A] [Preadditive A] [Linear R A]
    (p : R) (TI : A × A ⥤ A) (J : ObjectProperty (Aᵒᵖ × A))
    (HI : J.FullSubcategory ⥤ A) (SI : PodPartialClosed TI J HI)
    (T : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (H : (localizedPairs p J).FullSubcategory ⥤ ScalarLocalization R A p)
    (S : PodPartialClosed T (localizedPairs p J) H)
    (ht : (∀ MN, T.obj MN = ⟨TI.obj (MN.1.obj, MN.2.obj)⟩) ∧
      ∀ M M' N N', ∃ b : (M ⟶ M') →ₗ[Localization.Away p]
        (N ⟶ N') →ₗ[Localization.Away p] (T.obj (M, N) ⟶ T.obj (M', N')),
        (∀ a b', T.map (Prod.mkHom a b') = b a b') ∧
        ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (a b' : Localization.Away p),
          HEq (b (a ⊗ₜ[R] f) (b' ⊗ₜ[R] g))
            ((a * b') ⊗ₜ[R] TI.map (Prod.mkHom f g)))
    (hh : (∀ P, H.obj P = ⟨HI.obj (underlyingPair p J P)⟩) ∧
      ∀ P Q, ∃ b : (Q.obj.1.unop ⟶ P.obj.1.unop) →ₗ[Localization.Away p]
        (P.obj.2 ⟶ Q.obj.2) →ₗ[Localization.Away p] (H.obj P ⟶ H.obj Q),
        (∀ f g, H.map (ObjectProperty.homMk (Prod.mkHom f.op g)) = b f g) ∧
        ∀ (f : Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj) (g : P.obj.2.obj ⟶ Q.obj.2.obj)
          (a b' : Localization.Away p),
          HEq (b (a ⊗ₜ[R] f) (b' ⊗ₜ[R] g))
            ((a * b') ⊗ₜ[R] HI.map (X := underlyingPair p J P) (Y := underlyingPair p J Q)
              (ObjectProperty.homMk (Prod.mkHom f.op g))))
    (hev : ∀ P, HEq (S.evaluation P)
      ((1 : Localization.Away p) ⊗ₜ[R] SI.evaluation (underlyingPair p J P)))
    (hn : ∀ P P' (g : P ⟶ P'),
      TI.map (Prod.mkHom (HI.map g) (𝟙 P'.obj.1.unop)) ≫ SI.evaluation P' =
        TI.map (Prod.mkHom (𝟙 (HI.obj P)) g.hom.1.unop) ≫ SI.evaluation P ≫ g.hom.2)
    (P P' : (localizedPairs p J).FullSubcategory) (g : P ⟶ P') :
    T.map (Prod.mkHom (H.map g) (𝟙 P'.obj.1.unop)) ≫ S.evaluation P' =
      T.map (Prod.mkHom (𝟙 (H.obj P)) g.hom.1.unop) ≫ S.evaluation P ≫ g.hom.2 := by
  let JB := localizedPairs p J
  let I := underlyingPair p J
  have hH (Q : JB.FullSubcategory) : H.obj Q = ⟨HI.obj (I Q)⟩ := hh.1 Q
  have ho (P : JB.FullSubcategory)
      (N : ScalarLocalization R A p) :
      T.obj (H.obj P, N) = ⟨TI.obj (HI.obj (I P), N.obj)⟩ := by
    rw [show H.obj P = _ from hh.1 P]
    exact ht.1 _
  obtain ⟨bh, heh, hph⟩ := hh.2 P P'
  obtain ⟨bt, het, hpt⟩ := ht.2 (H.obj P) (H.obj P') P'.obj.1.unop P'.obj.1.unop
  obtain ⟨bu, heu, hpu⟩ := ht.2 (H.obj P) (H.obj P) P'.obj.1.unop P.obj.1.unop
  have hid (Q : JB.FullSubcategory) :
      HEq (𝟙 (H.obj Q))
        ((1 : Localization.Away p)
          ⊗ₜ[R] (𝟙 (HI.obj (I Q)))) := by
    rw [show H.obj Q = _ from hh.1 Q]
    rfl
  have pure (a : Localization.Away p)
      (f : P'.obj.1.unop.obj ⟶ P.obj.1.unop.obj)
      (b : Localization.Away p)
      (k : P.obj.2.obj ⟶ P'.obj.2.obj) :
      bt (bh (a ⊗ₜ[R] f)
        (b ⊗ₜ[R] k)) (𝟙 _) ≫ S.evaluation P' =
      bu (𝟙 _) (a ⊗ₜ[R] f) ≫
        S.evaluation P ≫ (b ⊗ₜ[R] k) := by
    let gi : I P ⟶ I P' := ObjectProperty.homMk (Prod.mkHom f.op k)
    have hl : HEq
        (bt (bh (a ⊗ₜ[R] f)
          (b ⊗ₜ[R] k)) (𝟙 _))
        (((a * b) * 1) ⊗ₜ[R]
          TI.map (Prod.mkHom (HI.map gi) (𝟙 P'.obj.1.unop.obj))) := by
      rw [← het, ← heh]
      exact tensorMap_heq _ TI T ht.2 (hH P) (hH P') rfl rfl
        (HI.map gi) (𝟙 _) (a * b) 1 (by rw [heh]; exact hph f k a b) HEq.rfl
    have hr : HEq (bu (𝟙 _) (a ⊗ₜ[R] f))
        ((1 * a) ⊗ₜ[R]
          TI.map (Prod.mkHom (𝟙 (HI.obj (I P))) f)) := by
      rw [← heu]
      exact tensorMap_heq _ TI T ht.2 (hH P) (hH P) rfl rfl
        (𝟙 _) f 1 a (hid P) HEq.rfl
    have lhs := heq_comp (ho P P'.obj.1.unop) (ho P' P'.obj.1.unop) rfl
      hl (hev P')
    have he : HEq (S.evaluation P ≫ (b ⊗ₜ[R] k))
        (ScalarLocalization.composition R A p _ _ _
          (b ⊗ₜ[R] k) (1 ⊗ₜ[R] SI.evaluation (I P))) :=
      heq_comp (ho P P.obj.1.unop) rfl rfl (hev P) HEq.rfl
    have rhs := heq_comp (ho P P'.obj.1.unop) (ho P P.obj.1.unop) rfl hr he
    apply eq_of_heq
    refine lhs.trans ((heq_of_eq ?_).trans rhs.symm)
    change ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ[_] SI.evaluation (I P'))
        (((a * b) * 1) ⊗ₜ[_] TI.map (Prod.mkHom (HI.map gi) (𝟙 _))) =
      ScalarLocalization.composition _ _ _ _ _ _
        (ScalarLocalization.composition _ _ _ _ _ _
          (b ⊗ₜ[_] k) (1 ⊗ₜ[_] SI.evaluation (I P)))
        ((1 * a) ⊗ₜ[_] TI.map (Prod.mkHom (𝟙 _) f))
    simp only [ScalarLocalization.composition_tmul, mul_one, one_mul]
    rw [mul_comm b a]
    exact congrArg (fun v ↦ (a * b) ⊗ₜ[R] v)
      (hn (I P) (I P') gi)
  have all (f : P'.obj.1.unop ⟶ P.obj.1.unop) (k : P.obj.2 ⟶ P'.obj.2) :
      bt (bh f k) (𝟙 _) ≫ S.evaluation P' =
        bu (𝟙 _) f ≫ S.evaluation P ≫ k := by
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, zero_comp]
    | tmul a f =>
      induction k using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero, LinearMap.zero_apply, zero_comp]
        change 0 = _ ≫ (S.evaluation P ≫ (0 : P.obj.2 ⟶ P'.obj.2))
        rw [comp_zero, comp_zero]
      | tmul b k => exact pure a f b k
      | add k k' hk hk' =>
        rw [map_add, map_add, LinearMap.add_apply, Preadditive.add_comp, hk, hk']
        have hadd := Preadditive.comp_add (C := ScalarLocalization R A p)
          _ _ _ (S.evaluation P) k k'
        rw [hadd]
        exact (Preadditive.comp_add (C := ScalarLocalization R A p) _ _ _
          (bu (𝟙 _) (a ⊗ₜ[R] f)) (S.evaluation P ≫ k) (S.evaluation P ≫ k')).symm
    | add f f' hf hf' =>
      simp only [map_add, LinearMap.add_apply, Preadditive.add_comp,
        hf, hf']
  have hg : g = ObjectProperty.homMk (Prod.mkHom g.hom.1.unop.op g.hom.2) := by
    apply ObjectProperty.hom_ext
    rfl
  rw [hg, heh, het, heu]
  exact all _ _

attribute [local irreducible] rationalDerivedTensor rationalDerivedInternalHom
  podRationalClosed

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
  refine localizedEvaluation_naturality
    (Padic.coefficientExtensionUniformizer l E) (constructibleIntegralTensor l E W)
    (constructibleIntegralHomPairs l E W) (constructibleIntegralHom l E W)
    (podIntegralClosed l E W) (rationalDerivedTensor l E W)
    (rationalDerivedInternalHom l E W) (podRationalClosed l E W)
    ?_ ?_ (rationalEvaluation_normalization l E W)
    (integralEvaluation_naturality l E W) P P' g
  · unfold rationalDerivedTensor
    exact (rationalDerivedTensor_existsUnique l E W).exists.choose_spec
  · unfold rationalDerivedInternalHom
    exact (rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec

end WeilConjectures
