/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SmoothPurity.Integral.IntegralDerivedHomBilinear

/-! # Nondegeneracy of normalized rational evaluation

Source: blueprint thm-coef-rational-verdier, evaluation and transposition.
(blueprint: lem-coef-rational-verdier-evaluation-detection). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

private def precompIsoLinear
    (R : Type*) [CommRing R] {C : Type*} [Category* C]
    [Preadditive C] [Linear R C] {P Q : C} (i : P ≅ Q) (W : C) :
    (P ⟶ W) ≃ₗ[R] (Q ⟶ W) where
  toFun f := i.inv ≫ f
  invFun f := i.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp
  map_smul' a f := by simp

private def adjHomLinearEquiv
    (R : Type*) [CommRing R] {C : Type*} [Category* C]
    [Preadditive C] [Linear R C] {F G : C ⥤ C}
    (adj : F ⊣ G) [G.Additive] [G.Linear R] (P Q : C) :
    (F.obj P ⟶ Q) ≃ₗ[R] (P ⟶ G.obj Q) where
  toEquiv := adj.homEquiv P Q
  map_add' f g := by simp [Adjunction.homEquiv_unit]
  map_smul' a f := by simp [Adjunction.homEquiv_unit]

-- A pairing with an integral linear transpose is its scalar-extended transpose.
private theorem pairing_baseChange
    {R : Type*} [CommRing R] {C : Type*} [Category* C]
    [Preadditive C] [Linear R C] (t : R) (P Q V U W : C)
    (P' Q' : ScalarLocalization R C t)
    (hP : P' = @ScalarLocalization.mk R C t P) (hQ : Q' = @ScalarLocalization.mk R C t Q)
    (b : (@ScalarLocalization.mk R C t V ⟶ @ScalarLocalization.mk R C t U) →ₗ[Localization.Away t]
      (P' ⟶ Q'))
    (m : (V ⟶ U) → (P ⟶ Q))
    (hp : ∀ (a : Localization.Away t) (f : V ⟶ U),
      HEq (b (a ⊗ₜ[R] f)) (a ⊗ₜ[R] m f))
    (e₀ : Q ⟶ W) (e : Q' ⟶ @ScalarLocalization.mk R C t W)
    (he : HEq e ((ScalarLocalization.localization R C t).map e₀))
    (L : (V ⟶ U) ≃ₗ[R] (P ⟶ W)) (hL : ∀ f, L f = m f ≫ e₀)
    (f : @ScalarLocalization.mk R C t V ⟶ @ScalarLocalization.mk R C t U) :
    b f ≫ e = eqToHom hP ≫ (L.baseChange R (Localization.Away t)) f := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    apply eq_of_heq
    refine (heq_comp hP hQ rfl (hp a f) he).trans ?_
    refine HEq.trans ?_ (eqToHom_comp_heq
      ((L.baseChange R (Localization.Away t)) (a ⊗ₜ[R] f)) hP).symm
    apply heq_of_eq
    change ScalarLocalization.composition R C t P Q W (1 ⊗ₜ[R] e₀)
      (a ⊗ₜ[R] m f) = _
    rw [ScalarLocalization.composition_tmul, one_mul, LinearEquiv.baseChange_tmul, hL]
  | add f g hf hg =>
    rw [map_add, Preadditive.add_comp, map_add]
    exact (congrArg₂ (· + ·) hf hg).trans (Preadditive.comp_add _ _ _ _ _ _).symm

-- Allow a propositionally equal localized dual object, as in Datum.objects.
private theorem pairing_injective
    {R : Type*} [CommRing R] {C : Type*} [Category* C]
    [Preadditive C] [Linear R C] (t : R) (P Q V U W : C)
    (P' Q' U' : ScalarLocalization R C t)
    (hP : P' = @ScalarLocalization.mk R C t P) (hQ : Q' = @ScalarLocalization.mk R C t Q)
    (hU : U' = @ScalarLocalization.mk R C t U)
    (b : (@ScalarLocalization.mk R C t V ⟶ U') →ₗ[Localization.Away t] (P' ⟶ Q'))
    (m : (V ⟶ U) → (P ⟶ Q))
    (hp : ∀ (a : Localization.Away t) (f : V ⟶ U),
      HEq (b ((a ⊗ₜ[R] f : @ScalarLocalization.mk R C t V ⟶ @ScalarLocalization.mk R C t U) ≫
        eqToHom hU.symm)) (a ⊗ₜ[R] m f))
    (e₀ : Q ⟶ W) (e : Q' ⟶ @ScalarLocalization.mk R C t W)
    (he : HEq e ((ScalarLocalization.localization R C t).map e₀))
    (L : (V ⟶ U) ≃ₗ[R] (P ⟶ W)) (hL : ∀ f, L f = m f ≫ e₀)
    (f g : @ScalarLocalization.mk R C t V ⟶ U') (h : b f ≫ e = b g ≫ e) : f = g := by
  subst U'
  simp only [eqToHom_refl, Category.comp_id] at hp
  have hh := pairing_baseChange t P Q V U W P' Q' hP hQ b m hp e₀ e he L hL
  apply (L.baseChange R (Localization.Away t)).injective
  apply (cancel_epi (eqToHom hP)).1
  rw [← hh f, ← hh g]
  exact h

private theorem tensor_map_heq {C : Type*} [Category* C] (B : C × C ⥤ C)
    {X X' Y Y' M M' N N' : C}
    (hx : X = X') (hy : Y = Y') (hm : M = M') (hn : N = N')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : M ⟶ N} {g' : M' ⟶ N'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (B.map (Prod.mkHom f g)) (B.map (Prod.mkHom f' g')) := by
  cases hx; cases hy; cases hm; cases hn; cases hf; cases hg
  rfl

namespace WeilConjectures.RationalVerdier

attribute [local irreducible] rationalDerivedTensor
attribute [local implicit_reducible] constructibleIntegralTensor
  IntegralVerdier.restrictedDual IntegralVerdier.dual integralDerivedInternalHom

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (w : IntegralFiniteExtension.DualizingDatum l X D hl E)

private instance homRight_additive (K : IntegralVerdier.Ambient l E X) :
    ((Functor.curry.obj (IntegralHom.hom.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))).obj (op K)).Additive := by
  constructor
  intro M N f g
  obtain ⟨b, hb⟩ := integralDerivedHom_bilinear l E X K K M N
  change (integralDerivedInternalHom l E X).map
      (Prod.mkHom (Quiver.Hom.op (𝟙 K)) (f + g)) =
    (integralDerivedInternalHom l E X).map (Prod.mkHom (Quiver.Hom.op (𝟙 K)) f) +
      (integralDerivedInternalHom l E X).map (Prod.mkHom (Quiver.Hom.op (𝟙 K)) g)
  simpa only [hb] using (b (𝟙 K)).map_add f g

private instance homRight_linear (K : IntegralVerdier.Ambient l E X) :
    ((Functor.curry.obj (IntegralHom.hom.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))).obj (op K)).Linear
        (Padic.coefficientExtensionIntegers l E) := by
  constructor
  intro M N f c
  obtain ⟨b, hb⟩ := integralDerivedHom_bilinear l E X K K M N
  change (integralDerivedInternalHom l E X).map
      (Prod.mkHom (Quiver.Hom.op (𝟙 K)) (c • f)) =
    c • (integralDerivedInternalHom l E X).map (Prod.mkHom (Quiver.Hom.op (𝟙 K)) f)
  simpa only [hb] using (b (𝟙 K)).map_smul c f

private abbrev integralDual (A : Datum D l hl X E w) :=
  IntegralVerdier.restrictedDual l E X w.omega.obj A.preserves

private def integralEvaluation (A : Datum D l hl X E w)
    (K : sfIntegralConstructibleCategory l E X) :
    (integralTensor D l hl X E).obj (K, (integralDual D l hl X E w A).obj (op K)) ⟶
      w.omega :=
  ObjectProperty.homMk
    ((@asIso _ _ _ _ (A.completion.map.app
      (K.obj, ((integralDual D l hl X E w A).obj (op K)).obj))
      (A.completion.invertible K ((integralDual D l hl X E w A).obj (op K)))).inv ≫
      (A.ordinary.adjunction K.obj).counit.app w.omega.obj)

-- Restrict ambient currying to the full subcategory and conjugate by completion.
private def integralHomEquiv (A : Datum D l hl X E w)
    (K V : sfIntegralConstructibleCategory l E X) :
    (V ⟶ (integralDual D l hl X E w A).obj (op K)) ≃ₗ[
      Padic.coefficientExtensionIntegers l E]
      ((integralTensor D l hl X E).obj (K, V) ⟶ w.omega) :=
  (InducedCategory.homLinearEquiv
    (R := Padic.coefficientExtensionIntegers l E)
    (F := fun Z : sfIntegralConstructibleCategory l E X ↦ Z.obj)
    (X := V) (Y := (integralDual D l hl X E w A).obj (op K))).trans
    (((adjHomLinearEquiv (Padic.coefficientExtensionIntegers l E)
      (A.ordinary.adjunction K.obj) V.obj w.omega.obj).symm.trans
      (precompIsoLinear (Padic.coefficientExtensionIntegers l E)
        (@asIso _ _ _ _ (A.completion.map.app (K.obj, V.obj))
          (A.completion.invertible K V)) w.omega.obj)).trans
      (InducedCategory.homLinearEquiv
        (R := Padic.coefficientExtensionIntegers l E)
        (F := fun Z : sfIntegralConstructibleCategory l E X ↦ Z.obj)
        (X := (integralTensor D l hl X E).obj (K, V)) (Y := w.omega)).symm)

private theorem integralHomEquiv_apply (A : Datum D l hl X E w)
    (K V : sfIntegralConstructibleCategory l E X)
    (f : V ⟶ (integralDual D l hl X E w A).obj (op K)) :
    integralHomEquiv D l hl X E w A K V f =
      (integralTensor D l hl X E).map (Prod.mkHom (𝟙 K) f) ≫
        integralEvaluation D l hl X E w A K := by
  let DK := (integralDual D l hl X E w A).obj (op K)
  let := A.completion.invertible K V
  let := A.completion.invertible K DK
  apply ObjectProperty.hom_ext
  change inv (A.completion.map.app (K.obj, V.obj)) ≫
      ((A.ordinary.adjunction K.obj).homEquiv V.obj w.omega.obj).symm f.hom =
    (integralCompletedTensor l E X).map (Prod.mkHom (𝟙 K.obj) f.hom) ≫
      inv (A.completion.map.app (K.obj, DK.obj)) ≫
        (A.ordinary.adjunction K.obj).counit.app w.omega.obj
  rw [Adjunction.homEquiv_counit]
  apply (cancel_epi (A.completion.map.app (K.obj, V.obj))).1
  simp only [← Category.assoc]
  rw [← A.completion.map.naturality (Prod.mkHom (𝟙 K.obj) f.hom)]
  simp only [DK, Category.assoc, IsIso.hom_inv_id_assoc, Functor.curry_obj_obj_map]

private theorem chosen_spec {T : Sort*} {p : T → Prop} (h : ∃ a, p a)
    (a : T) (ha : a = h.choose) : p a := ha.symm ▸ h.choose_spec

/-- The normalized rational evaluation detects maps into its dual object.
Source: blueprint thm-coef-rational-verdier, paragraph 1, evaluation and transposition;
Stacks 08J9. (blueprint: lem-coef-rational-verdier-evaluation-detection).

Proof: identify the rational dual with the localized restricted integral internal Hom
using A.objects. For fixed integral K and V, the ordinary tensor-Hom adjunction gives
an O_E-linear bijection from Hom(V,RHom(K,omega)) to Hom(K tensor V,omega). Its inverse
is composition of the ordinary tensor arrow with the ordinary counit; linearity follows
from the normalized internal Hom and the adjunction identities. Conjugate the target
by the invertible completion comparison on (K,V). Naturality of completion identifies
the resulting map with completed tensor followed by integral evaluation. Tensor this
linear equivalence with the localized coefficient ring. The rational tensor's bilinear
pure-tensor equation, the pure-tensor composition equation, and A.evaluation_integral
identify its action on every pure tensor with rational tensor followed by evaluation.
Both maps are additive, so the identity extends to arbitrary localized morphisms.
This base-changed linear equivalence is injective, giving f=g. Every raw rational K,V
has its stored integral object as representative, so the argument covers every input;
zero objects and the empty scheme cause no exception. -/
theorem rational_evaluation_detect (A : Datum D l hl X E w)
    (K V : sfRationalConstructibleCategory l E X)
    (f g : V ⟶ A.dual.obj (op K))
    (h : (tensor D l hl X E).map (Prod.mkHom (𝟙 K) f) ≫ A.evaluation K =
      (tensor D l hl X E).map (Prod.mkHom (𝟙 K) g) ≫ A.evaluation K) : f = g := by
  classical
  let B := tensor D l hl X E
  let T := integralTensor D l hl X E
  let J := sfRationalConstructibleLocalization l E X
  let DK := (integralDual D l hl X E w A).obj (op K.obj)
  have hs := chosen_spec
    (@rationalDerivedTensor_existsUnique l _ E _ _ _ X (units D l hl X)).exists
    B (by dsimp only [B, tensor]; unfold rationalDerivedTensor; rfl)
  have hD : A.dual.obj (op K) = J.obj DK := A.objects K
  have hP : B.obj (K, V) = J.obj (T.obj (K.obj, V.obj)) := hs.1 _
  have hQ : B.obj (K, A.dual.obj (op K)) = J.obj (T.obj (K.obj, DK)) :=
    (congrArg (fun N ↦ B.obj (K, N)) hD).trans (hs.1 _)
  obtain ⟨b, hb, _⟩ := hs.2 K K V (A.dual.obj (op K))
  refine pairing_injective (Padic.coefficientExtensionUniformizer l E)
    (T.obj (K.obj, V.obj)) (T.obj (K.obj, DK)) V.obj DK w.omega
    (B.obj (K, V)) (B.obj (K, A.dual.obj (op K))) (A.dual.obj (op K))
    hP hQ hD (b (𝟙 K)) (fun z ↦ T.map (Prod.mkHom (𝟙 K.obj) z)) ?_
    (integralEvaluation D l hl X E w A K.obj) (A.evaluation K) ?_
    (integralHomEquiv D l hl X E w A K.obj V.obj)
    (integralHomEquiv_apply D l hl X E w A K.obj V.obj) f g ?_
  · intro a z
    obtain ⟨b', hb', hp'⟩ := hs.2 K K V (J.obj DK)
    have hz : HEq
        ((a ⊗ₜ[Padic.coefficientExtensionIntegers l E] z : V ⟶ J.obj DK) ≫
          eqToHom hD.symm)
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] z : V ⟶ J.obj DK) :=
      comp_eqToHom_heq _ hD.symm
    exact (heq_of_eq (hb _ _).symm).trans
      ((tensor_map_heq B rfl rfl rfl hD HEq.rfl hz).trans
        ((heq_of_eq (hb' _ _)).trans ((hp' (𝟙 K.obj) z 1 a).trans (by
          simp only [one_mul]; rfl))))
  · exact A.evaluation_integral K.obj
  · simpa only [← hb, B, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using h

end WeilConjectures.RationalVerdier
