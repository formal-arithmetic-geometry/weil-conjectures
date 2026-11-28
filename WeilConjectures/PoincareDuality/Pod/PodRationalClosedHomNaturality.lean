/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase
import all WeilConjectures.PoincareDuality.Pod.Integral.PodIntegralHomComparisonNaturality

/-! # Naturality of rational inverse transposition in the Hom pair

For a rational partial closed datum with the pure-tensor normalization, inverse
transposition is natural in the permitted Hom pair: precomposing with the internal Hom
of a pair arrow `(a, b)` corresponds to tensoring with `a` and postcomposing with `b`.

## Main statements

* `localizedInverseTranspose_homNaturality`: the statement for an arbitrary scalar
  localization of a closed datum with bilinear tensor and Hom actions.
* `podRationalClosed_symm_comp_map`: the statement for rational constructible complexes.

## Implementation details

All maps are additive in each of the three localized arrows, so tensor induction reduces
the identity to pure tensors, where it is the integral identity tensored with a scalar.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

section Localization
open TensorProduct
variable {R : Type*} [CommRing R] {A : Type*} [Category* A]
  [Preadditive A] [Linear R A]

-- Induction on localized arrows into an object with a recorded integral representative.
private theorem localizedHom_induction (p : R)
    (M N : ScalarLocalization R A p) (N₀ : A) (hN : N = ⟨N₀⟩)
    (Q : (M ⟶ N) → Prop) (q : M ⟶ N)
    (ht : ∀ (a : Localization.Away p) (f : M.obj ⟶ N₀) (q : M ⟶ N),
      HEq q (a ⊗ₜ[R] f) → Q q)
    (ha : ∀ q q', Q q → Q q' → Q (q + q')) : Q q := by
  cases hN
  induction q using TensorProduct.inductionOn with
  | tmul a f => exact ht a f _ HEq.rfl
  | add q q' hq hq' => exact ha q q' hq hq'

/-- In a scalar localization, inverse transposition is natural in the Hom pair as soon as
it is so integrally and the tensor, Hom and inverse transposition maps are the scalar
extensions of the integral ones on pure tensors. -/
theorem localizedInverseTranspose_homNaturality (p : R)
    (T₀ : A × A ⥤ A) {J₀ : ObjectProperty (Aᵒᵖ × A)} (H₀ : J₀.FullSubcategory ⥤ A)
    (S₀ : PodPartialClosed T₀ J₀ H₀)
    (hS₀ : ∀ (L : A) (P Q : J₀.FullSubcategory) (h : P ⟶ Q) (φ : L ⟶ H₀.obj P),
      (S₀.transpose L Q).symm (φ ≫ H₀.map h) =
        T₀.map (Prod.mkHom (𝟙 L) h.hom.1.unop) ≫ (S₀.transpose L P).symm φ ≫ h.hom.2)
    (T : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (hTo : ∀ MN, T.obj MN = ⟨T₀.obj (MN.1.obj, MN.2.obj)⟩)
    (hTm : ∀ (M M' N N' : ScalarLocalization R A p),
      ∃ b : (M ⟶ M') →ₗ[Localization.Away p] (N ⟶ N') →ₗ[Localization.Away p]
          (T.obj (M, N) ⟶ T.obj (M', N')),
        (∀ a b', T.map (Prod.mkHom a b') = b a b') ∧
        ∀ (a : M.obj ⟶ M'.obj) (b' : N.obj ⟶ N'.obj) (c d : Localization.Away p),
          HEq (b (c ⊗ₜ[R] a) (d ⊗ₜ[R] b')) ((c * d) ⊗ₜ[R] T₀.map (Prod.mkHom a b')))
    {J : ObjectProperty ((ScalarLocalization R A p)ᵒᵖ × ScalarLocalization R A p)}
    (hJ : ∀ MN, J MN → J₀ (op MN.1.unop.obj, MN.2.obj))
    (H : J.FullSubcategory ⥤ ScalarLocalization R A p)
    (hHo : ∀ P : J.FullSubcategory,
      H.obj P = ⟨H₀.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩⟩)
    (hHm : ∀ P Q : J.FullSubcategory,
      ∃ b : (Q.obj.1.unop ⟶ P.obj.1.unop) →ₗ[Localization.Away p]
          (P.obj.2 ⟶ Q.obj.2) →ₗ[Localization.Away p] (H.obj P ⟶ H.obj Q),
        (∀ a b', H.map (ObjectProperty.homMk (Prod.mkHom a.op b')) = b a b') ∧
        ∀ (a : Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj) (b' : P.obj.2.obj ⟶ Q.obj.2.obj)
          (c d : Localization.Away p),
          HEq (b (c ⊗ₜ[R] a) (d ⊗ₜ[R] b'))
            ((c * d) ⊗ₜ[R] H₀.map
              (X := ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩)
              (Y := ⟨(op Q.obj.1.unop.obj, Q.obj.2.obj), hJ _ Q.property⟩)
              (ObjectProperty.homMk (Prod.mkHom a.op b'))))
    (S : PodPartialClosed T J H)
    (hS : ∀ (L : ScalarLocalization R A p) (P : J.FullSubcategory)
      (f : L.obj ⟶ H₀.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩)
      (a : Localization.Away p) (q : L ⟶ H.obj P),
      HEq q (a ⊗ₜ[R] f) →
        HEq ((S.transpose L P).symm q) (a ⊗ₜ[R] (S₀.transpose L.obj _).symm f))
    (L : ScalarLocalization R A p) (P Q : J.FullSubcategory)
    (a : Q.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ Q.obj.2) (φ : L ⟶ H.obj P) :
    (S.transpose L Q).symm (φ ≫ H.map (ObjectProperty.homMk (Prod.mkHom a.op b))) =
      T.map (Prod.mkHom (𝟙 L) a) ≫ (S.transpose L P).symm φ ≫ b := by
  obtain ⟨bH, hbH, hbHp⟩ := hHm P Q
  obtain ⟨bT, hbT, hbTp⟩ := hTm L L Q.obj.1.unop P.obj.1.unop
  rw [hbH, hbT]
  -- The pure-tensor case.
  have pure (c₁ : Localization.Away p) (a₀ : Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj)
      (c₂ : Localization.Away p) (b₀ : P.obj.2.obj ⟶ Q.obj.2.obj)
      (c₃ : Localization.Away p)
      (φ₀ : L.obj ⟶ H₀.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩)
      (q : L ⟶ H.obj P) (hq : HEq q (c₃ ⊗ₜ[R] φ₀)) :
      (S.transpose L Q).symm (q ≫ bH (c₁ ⊗ₜ[R] a₀) (c₂ ⊗ₜ[R] b₀)) =
        bT (𝟙 L) (c₁ ⊗ₜ[R] a₀) ≫ (S.transpose L P).symm q ≫
          (c₂ ⊗ₜ[R] b₀ : _) := by
    have h₁ := heq_comp rfl (hHo P) (hHo Q) hq (hbHp a₀ b₀ c₁ c₂)
    have h₂ := hS L Q _ _ _ (h₁.trans (heq_of_eq
      (ScalarLocalization.composition_tmul R A p _ _ _ _ _ _ _)))
    have h₃ := hbTp (𝟙 L.obj) a₀ 1 c₁
    have h₄ := hS L P φ₀ c₃ q hq
    have h₅ := heq_comp (hTo _) (hTo _) rfl h₃
      (heq_comp (hTo _) rfl rfl h₄ (HEq.refl (c₂ ⊗ₜ[R] b₀ :
        (⟨P.obj.2.obj⟩ : ScalarLocalization R A p) ⟶ ⟨Q.obj.2.obj⟩)))
    apply eq_of_heq
    refine h₂.trans (HEq.trans ?_ h₅.symm)
    apply heq_of_eq
    change _ = ScalarLocalization.composition R A p _ _ _
      (ScalarLocalization.composition R A p _ _ _ (c₂ ⊗ₜ[R] b₀)
        (c₃ ⊗ₜ[R] (S₀.transpose L.obj _).symm φ₀)) ((1 * c₁) ⊗ₜ[R] _)
    rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul]
    exact (congrArg ((c₁ * c₂ * c₃) ⊗ₜ[R] ·)
      (hS₀ L.obj _ _ (ObjectProperty.homMk
        (X := ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩)
        (Y := ⟨(op Q.obj.1.unop.obj, Q.obj.2.obj), hJ _ Q.property⟩)
        (Prod.mkHom a₀.op b₀)) φ₀)).trans
        (congrArg (· ⊗ₜ[R] _) (by ring : c₁ * c₂ * c₃ = c₂ * c₃ * (1 * c₁)))
  induction a using TensorProduct.inductionOn with
  | tmul c₁ a₀ =>
    induction b using TensorProduct.inductionOn with
    | tmul c₂ b₀ =>
      apply localizedHom_induction p L (H.obj P) _ (hHo P) _ φ
      · exact fun c₃ φ₀ q hq ↦ pure c₁ a₀ c₂ b₀ c₃ φ₀ q hq
      · intro φ φ' hφ hφ'
        rw [Preadditive.add_comp, map_add, hφ, hφ', map_add, Preadditive.add_comp,
          Preadditive.comp_add]
    | add b b' hb hb' =>
      rw [map_add, Preadditive.comp_add, map_add, hb, hb', Preadditive.comp_add,
        Preadditive.comp_add]
  | add a a' ha ha' =>
    rw [map_add, LinearMap.add_apply, Preadditive.comp_add, map_add, ha, ha', map_add,
      Preadditive.add_comp]

end Localization

section Rational
open TensorProduct
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- For a rational partial closed datum with the pure-tensor normalization, inverse
transposition is natural in the permitted Hom pair. -/
theorem podRationalClosed_symm_comp_map
    (S : PodPartialClosed (rationalDerivedTensor l E W)
      (constructibleRationalHomPairs l E W) (rationalDerivedInternalHom l E W))
    (hS : ∀ (L : sfRationalConstructibleCategory l E W)
      (P : (constructibleRationalHomPairs l E W).FullSubcategory)
      (f : L.obj ⟶ (constructibleIntegralHom l E W).obj
        (integralPairOfRationalHomPair l E W P))
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
      (q : L ⟶ (rationalDerivedInternalHom l E W).obj P),
      HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) →
      HEq ((S.transpose L P).symm q)
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          ((podIntegralClosed l E W).transpose L.obj
            (integralPairOfRationalHomPair l E W P)).symm f))
    (L : sfRationalConstructibleCategory l E W)
    (P Q : (constructibleRationalHomPairs l E W).FullSubcategory) (h : P ⟶ Q)
    (φ : L ⟶ (rationalDerivedInternalHom l E W).obj P) :
    (S.transpose L Q).symm (φ ≫ (rationalDerivedInternalHom l E W).map h) =
      (rationalDerivedTensor l E W).map (Prod.mkHom (𝟙 L) h.hom.1.unop) ≫
        (S.transpose L P).symm φ ≫ h.hom.2 := by
  have hT := (rationalDerivedTensor_existsUnique l E W).exists.choose_spec
  have hH := (rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec
  refine localizedInverseTranspose_homNaturality (Padic.coefficientExtensionUniformizer l E)
    (constructibleIntegralTensor l E W) (constructibleIntegralHom l E W)
    (podIntegralClosed l E W) ?_ (rationalDerivedTensor l E W) hT.1 hT.2
    (fun _ h ↦ h) (rationalDerivedInternalHom l E W) hH.1 hH.2 S hS L P Q
    h.hom.1.unop h.hom.2 φ
  intro L P Q h φ
  simpa only [Category.id_comp] using
    integralInverseTranspose_naturality l E W L L P Q (𝟙 L) h φ

end Rational

end WeilConjectures
