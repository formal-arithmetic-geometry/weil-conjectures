/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorNormalization
public import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityModelData
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Associativity of the ordinary quotient-system tensor comparison

Source: Stacks 03EK, 07A4 and 0941.

The ordinary tensor comparison of the strict quotient system is compatible with the
native total associators before localization. Chain maps of strict systems are tested
on all finite evaluations; there the tensor comparison becomes the normalized scalar
tensor comparison, and both composites agree on unit insertions of triple generators.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  CategoryTheory.Functor.mapHomologicalComplex

section Formal

variable {A S L : Type*} [Category* A] [Category* S] [Category* L]
  (tA : A × A ⥤ A) (tS : S × S ⥤ S) (tL : L × L ⥤ L) (K : A ⥤ S) (Ev : S ⥤ L) (F : A ⥤ L)
  (θ : K ⋙ Ev ≅ F) (κ : tA ⋙ K ≅ K.prod K ⋙ tS)
  (e : ∀ X Y : S, Ev.obj (tS.obj (X, Y)) ≅ tL.obj (Ev.obj X, Ev.obj Y))
  (s : ∀ P Q : A, F.obj (tA.obj (P, Q)) ≅ tL.obj (F.obj P, F.obj Q))

/-- The left associativity composite of a tensor comparison, evaluated and transported to
the scalar coordinates, is the composite of the scalar tensor comparisons.
Source: Stacks 07A4. -/
theorem evaluated_tensor_left_composite
    (he : ∀ {X X' Y Y' : S} (f : X ⟶ X') (g : Y ⟶ Y'),
      Ev.map (tS.map (Prod.mkHom f g)) ≫ (e X' Y').hom =
        (e X Y).hom ≫ tL.map (Prod.mkHom (Ev.map f) (Ev.map g)))
    (hκ : ∀ P Q : A, Ev.map (κ.hom.app (P, Q)) ≫ (e (K.obj P) (K.obj Q)).hom ≫
        tL.map (Prod.mkHom (θ.hom.app P) (θ.hom.app Q)) =
      θ.hom.app (tA.obj (P, Q)) ≫ (s P Q).hom)
    (P Q N : A) :
    θ.inv.app (tA.obj (P, tA.obj (Q, N))) ≫
      Ev.map (κ.hom.app (P, tA.obj (Q, N)) ≫
        tS.map (Prod.mkHom (𝟙 (K.obj P)) (κ.hom.app (Q, N)))) ≫
      (e (K.obj P) (tS.obj (K.obj Q, K.obj N))).hom ≫
      tL.map (Prod.mkHom (θ.hom.app P) ((e (K.obj Q) (K.obj N)).hom ≫
        tL.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N)))) =
    (s P (tA.obj (Q, N))).hom ≫ tL.map (Prod.mkHom (𝟙 _) (s Q N).hom) := by
  have hsplit : tL.map (Prod.mkHom (θ.hom.app P) (θ.hom.app (tA.obj (Q, N)) ≫ (s Q N).hom)) =
      tL.map (Prod.mkHom (θ.hom.app P) (θ.hom.app (tA.obj (Q, N)))) ≫
        tL.map (Prod.mkHom (𝟙 _) (s Q N).hom) := by
    rw [← tL.map_comp]
    congr 1
    exact Prod.ext (Category.comp_id _).symm rfl
  have he' : Ev.map (tS.map (Prod.mkHom (𝟙 (K.obj P)) (κ.hom.app (Q, N)))) ≫
      (e (K.obj P) (tS.obj (K.obj Q, K.obj N))).hom =
      (e (K.obj P) (K.obj (tA.obj (Q, N)))).hom ≫
        tL.map (Prod.mkHom (Ev.map (𝟙 (K.obj P))) (Ev.map (κ.hom.app (Q, N)))) := he _ _
  rw [Ev.map_comp, Category.assoc, reassoc_of% he', ← tL.map_comp]
  have hc : Prod.mkHom (Ev.map (𝟙 (K.obj P))) (Ev.map (κ.hom.app (Q, N))) ≫
      Prod.mkHom (θ.hom.app P) ((e (K.obj Q) (K.obj N)).hom ≫
        tL.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N))) =
      Prod.mkHom (θ.hom.app P) (θ.hom.app (tA.obj (Q, N)) ≫ (s Q N).hom) := by
    refine Prod.ext ?_ ?_
    · exact (congrArg (· ≫ θ.hom.app P) (Ev.map_id _)).trans (Category.id_comp _)
    · exact hκ Q N
  rw [hc, hsplit, reassoc_of% (hκ P (tA.obj (Q, N))), Iso.inv_hom_id_app_assoc]

/-- The right associativity composite of a tensor comparison, evaluated and transported to
the scalar coordinates, is the composite of the scalar tensor comparisons followed by the
transported associator. Source: Stacks 07A4. -/
theorem evaluated_tensor_right_composite
    (he : ∀ {X X' Y Y' : S} (f : X ⟶ X') (g : Y ⟶ Y'),
      Ev.map (tS.map (Prod.mkHom f g)) ≫ (e X' Y').hom =
        (e X Y).hom ≫ tL.map (Prod.mkHom (Ev.map f) (Ev.map g)))
    (hκ : ∀ P Q : A, Ev.map (κ.hom.app (P, Q)) ≫ (e (K.obj P) (K.obj Q)).hom ≫
        tL.map (Prod.mkHom (θ.hom.app P) (θ.hom.app Q)) =
      θ.hom.app (tA.obj (P, Q)) ≫ (s P Q).hom)
    (P Q N : A) {Y : L}
    (b' : Ev.obj (tS.obj (tS.obj (K.obj P, K.obj Q), K.obj N)) ⟶ Y) :
    θ.inv.app (tA.obj (tA.obj (P, Q), N)) ≫
      Ev.map (κ.hom.app (tA.obj (P, Q), N) ≫
        tS.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (K.obj N)))) ≫ b' =
    (s (tA.obj (P, Q)) N).hom ≫ tL.map (Prod.mkHom (s P Q).hom (𝟙 _)) ≫
      tL.map (Prod.mkHom (tL.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q)) ≫
        (e (K.obj P) (K.obj Q)).inv) (θ.inv.app N)) ≫
      (e (tS.obj (K.obj P, K.obj Q)) (K.obj N)).inv ≫ b' := by
  have he' : Ev.map (tS.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (K.obj N)))) ≫
      (e (tS.obj (K.obj P, K.obj Q)) (K.obj N)).hom =
      (e (K.obj (tA.obj (P, Q))) (K.obj N)).hom ≫
        tL.map (Prod.mkHom (Ev.map (κ.hom.app (P, Q))) (Ev.map (𝟙 (K.obj N)))) := he _ _
  have hθ : tL.map (Prod.mkHom (θ.hom.app P) (θ.hom.app Q)) ≫
      tL.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q)) = 𝟙 _ := by
    rw [← tL.map_comp, ← tL.map_id]
    congr 1
    exact Prod.ext (Iso.hom_inv_id_app θ P) (Iso.hom_inv_id_app θ Q)
  have h1 : θ.hom.app (tA.obj (P, Q)) ≫ (s P Q).hom ≫
      tL.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q)) ≫ (e (K.obj P) (K.obj Q)).inv =
      Ev.map (κ.hom.app (P, Q)) := by
    rw [← reassoc_of% (hκ P Q), reassoc_of% hθ, Iso.hom_inv_id, Category.comp_id]
  have hsplit : tL.map (Prod.mkHom (Ev.map (κ.hom.app (P, Q))) (Ev.map (𝟙 (K.obj N)))) =
      tL.map (Prod.mkHom (θ.hom.app (tA.obj (P, Q))) (θ.hom.app N)) ≫
        tL.map (Prod.mkHom (s P Q).hom (𝟙 _)) ≫
        tL.map (Prod.mkHom (tL.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q)) ≫
          (e (K.obj P) (K.obj Q)).inv) (θ.inv.app N)) := by
    rw [← tL.map_comp, ← tL.map_comp]
    congr 1
    refine Prod.ext ?_ ?_
    · rw [← h1]
      rfl
    · simp
  have hs : (s (tA.obj (P, Q)) N).hom = θ.inv.app (tA.obj (tA.obj (P, Q), N)) ≫
      Ev.map (κ.hom.app (tA.obj (P, Q), N)) ≫ (e (K.obj (tA.obj (P, Q))) (K.obj N)).hom ≫
      tL.map (Prod.mkHom (θ.hom.app (tA.obj (P, Q))) (θ.hom.app N)) := by
    rw [hκ, Iso.inv_hom_id_app_assoc]
  rw [hs, Ev.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hsplit, ← reassoc_of% he', Iso.hom_inv_id_assoc]

/-- The left associativity composite in factored scalar coordinates.
Source: Stacks 07A4. -/
theorem evaluated_tensor_left_composite'
    (he : ∀ {X X' Y Y' : S} (f : X ⟶ X') (g : Y ⟶ Y'),
      Ev.map (tS.map (Prod.mkHom f g)) ≫ (e X' Y').hom =
        (e X Y).hom ≫ tL.map (Prod.mkHom (Ev.map f) (Ev.map g)))
    (hκ : ∀ P Q : A, Ev.map (κ.hom.app (P, Q)) ≫ (e (K.obj P) (K.obj Q)).hom ≫
        tL.map (Prod.mkHom (θ.hom.app P) (θ.hom.app Q)) =
      θ.hom.app (tA.obj (P, Q)) ≫ (s P Q).hom)
    (P Q N : A) {Y : A} (a : Y ⟶ tA.obj (P, tA.obj (Q, N))) :
    θ.inv.app Y ≫ Ev.map (K.map a ≫ κ.hom.app (P, tA.obj (Q, N)) ≫
        tS.map (Prod.mkHom (𝟙 (K.obj P)) (κ.hom.app (Q, N)))) ≫
      (e (K.obj P) (tS.obj (K.obj Q, K.obj N))).hom ≫
      tL.map (Prod.mkHom (𝟙 _) (e (K.obj Q) (K.obj N)).hom) ≫
      tL.map (Prod.mkHom (θ.hom.app P) (tL.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N)))) =
    F.map a ≫ (s P (tA.obj (Q, N))).hom ≫ tL.map (Prod.mkHom (𝟙 _) (s Q N).hom) := by
  have hc : tL.map (Prod.mkHom (𝟙 (Ev.obj (K.obj P))) (e (K.obj Q) (K.obj N)).hom) ≫
      tL.map (Prod.mkHom (θ.hom.app P) (tL.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N)))) =
      tL.map (Prod.mkHom (θ.hom.app P) ((e (K.obj Q) (K.obj N)).hom ≫
        tL.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N)))) := by
    rw [bifunctor_map_mkHom_comp, Category.id_comp]
  have hn : θ.inv.app Y ≫ Ev.map (K.map a) = F.map a ≫ θ.inv.app _ := (θ.inv.naturality a).symm
  rw [hc, Ev.map_comp_assoc, reassoc_of% hn,
    evaluated_tensor_left_composite tA tS tL K Ev F θ κ e s he hκ P Q N]

/-- The right associativity composite in factored scalar coordinates.
Source: Stacks 07A4. -/
theorem evaluated_tensor_right_composite'
    (he : ∀ {X X' Y Y' : S} (f : X ⟶ X') (g : Y ⟶ Y'),
      Ev.map (tS.map (Prod.mkHom f g)) ≫ (e X' Y').hom =
        (e X Y).hom ≫ tL.map (Prod.mkHom (Ev.map f) (Ev.map g)))
    (hκ : ∀ P Q : A, Ev.map (κ.hom.app (P, Q)) ≫ (e (K.obj P) (K.obj Q)).hom ≫
        tL.map (Prod.mkHom (θ.hom.app P) (θ.hom.app Q)) =
      θ.hom.app (tA.obj (P, Q)) ≫ (s P Q).hom)
    (P Q N : A) {Y : L}
    (b' : Ev.obj (tS.obj (tS.obj (K.obj P, K.obj Q), K.obj N)) ⟶ Y) :
    θ.inv.app (tA.obj (tA.obj (P, Q), N)) ≫
      Ev.map (κ.hom.app (tA.obj (P, Q), N) ≫
        tS.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (K.obj N)))) ≫ b' =
    (s (tA.obj (P, Q)) N).hom ≫ tL.map (Prod.mkHom (s P Q).hom (𝟙 _)) ≫
      tL.map (Prod.mkHom (tL.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q))) (θ.inv.app N)) ≫
      tL.map (Prod.mkHom (e (K.obj P) (K.obj Q)).inv (𝟙 (Ev.obj (K.obj N)))) ≫
      (e (tS.obj (K.obj P, K.obj Q)) (K.obj N)).inv ≫ b' := by
  have hc : tL.map (Prod.mkHom (tL.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q))) (θ.inv.app N)) ≫
      tL.map (Prod.mkHom (e (K.obj P) (K.obj Q)).inv (𝟙 (Ev.obj (K.obj N)))) =
      tL.map (Prod.mkHom (tL.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q)) ≫
        (e (K.obj P) (K.obj Q)).inv) (θ.inv.app N)) := by
    rw [bifunctor_map_mkHom_comp]
    erw [Category.comp_id]
  rw [reassoc_of% hc, evaluated_tensor_right_composite tA tS tL K Ev F θ κ e s he hκ P Q N b']

/-- A tensor comparison is compatible with given associators as soon as, after evaluation and
transport to the scalar coordinates, the reassociation of the scalar tensor comparisons is
the transported associator. Source: Stacks 07A4. -/
theorem evaluated_tensor_associativity
    (he : ∀ {X X' Y Y' : S} (f : X ⟶ X') (g : Y ⟶ Y'),
      Ev.map (tS.map (Prod.mkHom f g)) ≫ (e X' Y').hom =
        (e X Y).hom ≫ tL.map (Prod.mkHom (Ev.map f) (Ev.map g)))
    (hκ : ∀ P Q : A, Ev.map (κ.hom.app (P, Q)) ≫ (e (K.obj P) (K.obj Q)).hom ≫
        tL.map (Prod.mkHom (θ.hom.app P) (θ.hom.app Q)) =
      θ.hom.app (tA.obj (P, Q)) ≫ (s P Q).hom)
    (P Q N : A) (a : tA.obj (tA.obj (P, Q), N) ⟶ tA.obj (P, tA.obj (Q, N)))
    (b' : tS.obj (tS.obj (K.obj P, K.obj Q), K.obj N) ⟶
      tS.obj (K.obj P, tS.obj (K.obj Q, K.obj N)))
    (hA : F.map a ≫ (s P (tA.obj (Q, N))).hom ≫ tL.map (Prod.mkHom (𝟙 (F.obj P)) (s Q N).hom) =
      (s (tA.obj (P, Q)) N).hom ≫ tL.map (Prod.mkHom (s P Q).hom (𝟙 (F.obj N))) ≫
        tL.map (Prod.mkHom (tL.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q))) (θ.inv.app N)) ≫
        tL.map (Prod.mkHom (e (K.obj P) (K.obj Q)).inv (𝟙 (Ev.obj (K.obj N)))) ≫
        (e (tS.obj (K.obj P, K.obj Q)) (K.obj N)).inv ≫ Ev.map b' ≫
        (e (K.obj P) (tS.obj (K.obj Q, K.obj N))).hom ≫
        tL.map (Prod.mkHom (𝟙 (Ev.obj (K.obj P))) (e (K.obj Q) (K.obj N)).hom) ≫
        tL.map (Prod.mkHom (θ.hom.app P) (tL.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N))))) :
    Ev.map (K.map a ≫ κ.hom.app (P, tA.obj (Q, N)) ≫
        tS.map (Prod.mkHom (𝟙 (K.obj P)) (κ.hom.app (Q, N)))) =
      Ev.map (κ.hom.app (tA.obj (P, Q), N) ≫
        tS.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (K.obj N))) ≫ b') := by
  let Z := (e (K.obj P) (tS.obj (K.obj Q, K.obj N))).hom ≫
    tL.map (Prod.mkHom (𝟙 _) (e (K.obj Q) (K.obj N)).hom) ≫
    tL.map (Prod.mkHom (θ.hom.app P) (tL.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N))))
  have hL := evaluated_tensor_left_composite' tA tS tL K Ev F θ κ e s he hκ P Q N a
  have hR := evaluated_tensor_right_composite' tA tS tL K Ev F θ κ e s he hκ P Q N
    (Ev.map b' ≫ Z)
  have : IsIso Z := by
    have : IsIso (tL.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N))) :=
      isIso_bifunctor_map_mkHom tL _ _
    have : IsIso (tL.map (Prod.mkHom (θ.hom.app P)
        (tL.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N))))) :=
      isIso_bifunctor_map_mkHom tL _ _
    have : IsIso (tL.map (Prod.mkHom (𝟙 (Ev.obj (K.obj P))) (e (K.obj Q) (K.obj N)).hom)) :=
      isIso_bifunctor_map_mkHom tL _ _
    dsimp only [Z]
    infer_instance
  apply (cancel_epi (θ.inv.app (tA.obj (tA.obj (P, Q), N)))).mp
  apply (cancel_mono Z).mp
  have h1 := hL.trans (hA.trans hR.symm)
  simp only [Z, Ev.map_comp, Category.assoc] at h1 ⊢
  exact h1
end Formal

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Ordinary scalar extension of a map sends unit sections to unit sections.
Source: Stacks 03CZ, 06YY. -/
theorem coefficientIntegralScalarUnitSection_naturality (n : ℕ)
    {X X' : scalarReductionSource l E W} (φ : X ⟶ X') (V : W.ProEtᵒᵖ) (x : X.val.obj V) :
    ((scalarReductionExtension l E W n).map φ).val.app V
        (coefficientIntegralScalarUnitSection l E W n X V x) =
      coefficientIntegralScalarUnitSection l E W n X' V (φ.val.app V x) :=
  (congrArg (fun k ↦ k.val.app V x)
    ((coefficientOrdinaryScalarAdjunction l E W n).unit.naturality φ)).symm

/-- The unit-section formula characterizing the ordinary scalar tensor comparison.
Source: Stacks 03EK, 07A4. -/
theorem coefficientScalarTensorIso_hom_unitSection (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) (p q k : ℤ) (hpq : p + q = k)
    (V : W.ProEtᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    ((coefficientScalarTensorIso l E W n P Q).hom.f k).val.app V
      (coefficientIntegralScalarUnitSection l E W n _ V
        (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq V x y)) =
      coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq V
        (coefficientIntegralScalarUnitSection l E W n _ V x)
        (coefficientIntegralScalarUnitSection l E W n _ V y) := by
  unfold coefficientScalarTensorIso coefficientUniqueComparisonChoice
  exact (coefficientScalarTensorIso_exists l E W n P Q).choose_spec.1 p q k hpq V x y

/-- Chain maps out of the scalar extension of a triple total tensor agree once they agree on
unit insertions of triple tensor generators. Source: Stacks 03EK, 06YY, 07A4. -/
theorem scalarExtension_tripleTensor_hom_ext (n : ℕ)
    (P Q N : CochainComplex (scalarReductionSource l E W) ℤ)
    {Y : CochainComplex (scalarReductionTarget l E W n) ℤ}
    (f g : ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q), N)) ⟶ Y)
    (h : ∀ (p q r i k : ℤ) (hpq : p + q = i) (hik : i + r = k) (V : W.ProEtᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) (z : (N.X r).val.obj V),
      (f.f k).val.app V (coefficientIntegralScalarUnitSection l E W n _ V
        (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) _ N i r k hik V
          (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W) P Q p q i hpq V x y) z)) =
      (g.f k).val.app V (coefficientIntegralScalarUnitSection l E W n _ V
        (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) _ N i r k hik V
          (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W) P Q p q i hpq V x y) z))) :
    f = g := by
  let adj := (coefficientOrdinaryScalarAdjunction l E W n).mapHomologicalComplex (.up ℤ)
  apply (adj.homEquiv _ _).injective
  apply CategoryTheory.tensorGenerator_ext₃.{t + 1, t, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) P Q N
  intro p q r i k hpq hik V x y z
  exact h p q r i k hpq hik V x y z

namespace OrdinaryQuotient

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  coefficientEvaluationTensorIso coefficientScalarTensorIso coefficientUniqueComparisonChoice
  coefficientSequenceEvaluation coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology SheafOfModules.monoidalCategory

/-- Finite-level total-tensor maps act on generators by applying both input maps.
Source: Stacks 03EK, 07A4. -/
theorem normalizedDVR_tensorGenerator_map (n : ℕ)
    {P P' Q Q' : CochainComplex (normalizedDVRModules l E W n) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q k : ℤ) (h : p + q = k)
    (V : W.ProEtᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    (((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom f g)).f k).val.app V
        (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n) P Q p q k h V x y) =
      coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) P' Q' p q k h V
        ((f.f p).val.app V x) ((g.f q).val.app V y) :=
  CategoryTheory.ScalarHomTensor.tensor_generator_map.{t + 1, t, u} f g p q k h V x y

/-- The total associator of strict systems, evaluated and conjugated by the evaluation tensor
comparisons, reassociates finite tensor generators.
Source: Stacks 03EK, 07A4, 0941. -/
theorem evaluatedAssociator_generator (n : ℕ)
    (X Y Z : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (b' : (coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (X, Y), Z) ≅
      (coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        (X, (coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (Y, Z)))
    (hb' : CoefficientComplexAssociatorFormula
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) X Y Z b')
    (p q r pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + r = qr) (hk : pq + r = k)
    (hk' : p + qr = k) (U : W.ProEtᵒᵖ)
    (x : (X.X p).val.obj (op (n, U.unop))) (y : (Y.X q).val.obj (op (n, U.unop)))
    (z : (Z.X r).val.obj (op (n, U.unop))) :
    (((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom
          (coefficientEvaluationTensorIso l E W n X Y).inv (𝟙 _)) ≫
      (coefficientEvaluationTensorIso l E W n ((coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (X, Y)) Z).inv ≫
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map b'.hom ≫
      (coefficientEvaluationTensorIso l E W n X ((coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (Y, Z))).hom ≫
      (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom (𝟙 _)
          (coefficientEvaluationTensorIso l E W n Y Z).hom)).f k).val.app U
      (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) _ _ pq r k hk U
        (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n) _ _ p q pq hpq U
          (coefficientEvaluationSection l E W (X.X p) n U x)
          (coefficientEvaluationSection l E W (Y.X q) n U y))
        (coefficientEvaluationSection l E W (Z.X r) n U z)) =
    coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) _ _ p qr k hk' U
      (coefficientEvaluationSection l E W (X.X p) n U x)
      (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) _ _ q r qr hqr U
        (coefficientEvaluationSection l E W (Y.X q) n U y)
        (coefficientEvaluationSection l E W (Z.X r) n U z)) := by
  let T := coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  let T' := coefficientTotalTensor.{u, t + 1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
  let Ev := (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)
  let σ := fun (M : coefficientSequenceModules l E W) (w : M.val.obj (op (n, U.unop))) ↦
    coefficientEvaluationSection l E W M n U w
  let g := coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  let g' := coefficientTensorGenerator.{u, t + 1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
  have s1 : ((T.map (Prod.mkHom (coefficientEvaluationTensorIso l E W n X Y).inv
      (𝟙 (Ev.obj Z)))).f k).val.app U
        (g _ _ pq r k hk U (g _ _ p q pq hpq U (σ _ x) (σ _ y)) (σ _ z)) =
      g (Ev.obj (T'.obj (X, Y))) (Ev.obj Z) pq r k hk U (σ _ (g' X Y p q pq hpq _ x y))
        (σ _ z) := by
    rw [normalizedDVR_tensorGenerator_map, coefficientEvaluationTensorIso_inv_generator]
    rfl
  have s2 := coefficientEvaluationTensorIso_inv_generator l E W n (T'.obj (X, Y)) Z pq r k hk U
    (g' X Y p q pq hpq _ x y) z
  have s3 := coefficientEvaluationSection_map l E W (b'.hom.f k) n U
    (g' (T'.obj (X, Y)) Z pq r k hk _ (g' X Y p q pq hpq _ x y) z)
  have s4 := hb' p q r pq qr k hpq hqr hk hk' (op (n, U.unop)) x y z
  have s5 := coefficientEvaluationTensorIso_hom_generator l E W n X (T'.obj (Y, Z)) p qr k hk' U
    x (g' Y Z q r qr hqr _ y z)
  have s6 : ((T.map (Prod.mkHom (𝟙 (Ev.obj X)) (coefficientEvaluationTensorIso l E W n Y Z).hom)).f
      k).val.app U (g (Ev.obj X) (Ev.obj (T'.obj (Y, Z))) p qr k hk' U (σ _ x)
        (σ _ (g' Y Z q r qr hqr _ y z))) =
      g (Ev.obj X) (T.obj (Ev.obj Y, Ev.obj Z)) p qr k hk' U (σ _ x)
        (g (Ev.obj Y) (Ev.obj Z) q r qr hqr U (σ _ y) (σ _ z)) := by
    rw [normalizedDVR_tensorGenerator_map, coefficientEvaluationTensorIso_hom_generator]
    rfl
  exact (congrArg (fun w ↦ ((T.map (Prod.mkHom (𝟙 (Ev.obj X))
      (coefficientEvaluationTensorIso l E W n Y Z).hom)).f k).val.app U w)
    ((congrArg (fun w ↦ ((coefficientEvaluationTensorIso l E W n X (T'.obj (Y, Z))).hom.f
      k).val.app U w)
    ((congrArg (fun w ↦ ((Ev.map b'.hom).f k).val.app U w)
      ((congrArg (fun w ↦ ((coefficientEvaluationTensorIso l E W n (T'.obj (X, Y)) Z).inv.f
        k).val.app U w) s1).trans s2)).trans (s3.trans
      (congrArg (σ _) s4)))).trans s5)).trans s6

set_option maxHeartbeats 1600000 in
-- The unit-section comparison elaborates several large nested generator terms.
attribute [local semireducible] coefficientSequenceEvaluation in
/-- The scalar-coordinate form of tensor associativity for the quotient system: on unit
insertions of triple generators both composites are the reassociated generator.
Source: Stacks 03EK, 07A4, 0941. -/
theorem OrdinaryModel.scalarTensorAssociativity (M : OrdinaryModel l E W) (n : ℕ)
    (P Q N : CochainComplex (scalarReductionSource l E W) ℤ)
    (a : (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q), N) ≅
      (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj
        (P, (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (Q, N)))
    (ha : CoefficientComplexAssociatorFormula (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) P Q N a)
    (b' : (coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj
          ((M.quotient l E W).obj P, (M.quotient l E W).obj Q), (M.quotient l E W).obj N) ≅
      (coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((M.quotient l E W).obj P, (coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj
          ((M.quotient l E W).obj Q, (M.quotient l E W).obj N)))
    (hb' : CoefficientComplexAssociatorFormula
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
      ((M.quotient l E W).obj P) ((M.quotient l E W).obj Q) ((M.quotient l E W).obj N) b') :
    let T := coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
    let T' := coefficientTotalTensor.{u, t + 1, t}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
    let tA := coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
    let Ev := (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)
    let F := (scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)
    let K := M.quotient l E W
    let θ := NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)
    let e := coefficientEvaluationTensorIso l E W n
    let s := coefficientScalarTensorIso l E W n
    F.map a.hom ≫ (s P (tA.obj (Q, N))).hom ≫ T.map (Prod.mkHom (𝟙 (F.obj P)) (s Q N).hom) =
    (s (tA.obj (P, Q)) N).hom ≫ T.map (Prod.mkHom (s P Q).hom (𝟙 (F.obj N))) ≫
      T.map (Prod.mkHom (T.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q))) (θ.inv.app N)) ≫
      T.map (Prod.mkHom (e (K.obj P) (K.obj Q)).inv (𝟙 (Ev.obj (K.obj N)))) ≫
      (e (T'.obj (K.obj P, K.obj Q)) (K.obj N)).inv ≫ Ev.map b'.hom ≫
      (e (K.obj P) (T'.obj (K.obj Q, K.obj N))).hom ≫
      T.map (Prod.mkHom (𝟙 (Ev.obj (K.obj P))) (e (K.obj Q) (K.obj N)).hom) ≫
      T.map (Prod.mkHom (θ.hom.app P) (T.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N)))) := by
  dsimp only
  apply scalarExtension_tripleTensor_hom_ext l E W n P Q N
  intro p q r i k hpq hik V x y z
  let g := coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  let u := fun (X : scalarReductionSource l E W) (w : X.val.obj V) ↦
    coefficientIntegralScalarUnitSection l E W n X V w
  have hk' : p + (q + r) = k := by omega
  have L1 := coefficientIntegralScalarUnitSection_naturality l E W n (a.hom.f k) V
    (g _ N i r k hik V (g P Q p q i hpq V x y) z)
  have L2 := ha p q r i (q + r) k hpq rfl hik hk' V x y z
  have L3 := coefficientScalarTensorIso_hom_unitSection l E W n P
    ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (Q, N))
    p (q + r) k hk' V
    x (g Q N q r (q + r) rfl V y z)
  have L4 := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    (𝟙 (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P))
    (coefficientScalarTensorIso l E W n Q N).hom
    p (q + r) k hk' V (u _ x) (u _ (g Q N q r (q + r) rfl V y z))
  rw [coefficientScalarTensorIso_hom_unitSection] at L4
  have R1 := coefficientScalarTensorIso_hom_unitSection l E W n
    ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q))
    N i r k hik V
    (g P Q p q i hpq V x y) z
  have R2 := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    (coefficientScalarTensorIso l E W n P Q).hom
    (𝟙 (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj N))
    i r k hik V (u _ (g P Q p q i hpq V x y)) (u _ z)
  rw [coefficientScalarTensorIso_hom_unitSection] at R2
  let w := fun (X : scalarReductionSource l E W) (v : X.val.obj V) ↦
    ((M.adjunction.unit.app X ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj X)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (M.tensor.obj X)).val.app V v : (M.tensor.obj X).val.obj (op (n, V.unop)))
  have hθ (X : CochainComplex (scalarReductionSource l E W) ℤ) (j : ℤ) (v : (X.X j).val.obj V) :
      (((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app X).f j).val.app V
        (coefficientEvaluationSection l E W _ n V (w _ v)) = u _ v :=
    congrArg (fun f ↦ f.val.app V v) (M.unit_projection l E W (X.X j) n)
  have hθ' (X : CochainComplex (scalarReductionSource l E W) ℤ) (j : ℤ) (v : (X.X j).val.obj V) :
      (((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app X).f j).val.app V
        (u _ v) = coefficientEvaluationSection l E W _ n V (w _ v) := by
    rw [← hθ X j v]
    exact congrArg (fun φ ↦ (φ.f j).val.app V (coefficientEvaluationSection l E W _ n V (w _ v)))
      ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom_inv_id_app X)
  have R3a := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app P)
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app Q) p q i hpq V
    (u _ x) (u _ y)
  rw [hθ', hθ'] at R3a
  have R3b := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).map
        (Prod.mkHom ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app P)
          ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app Q)))
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app N) i r k hik V
    (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) _ _ p q i hpq V (u _ x) (u _ y)) (u _ z)
  rw [hθ'] at R3b
  have R4 := OrdinaryQuotient.evaluatedAssociator_generator l E W n ((M.quotient l E W).obj P)
    ((M.quotient l E W).obj Q) ((M.quotient l E W).obj N)
    b' hb' p q r i (q + r) k hpq rfl hik hk' V (w _ x) (w _ y) (w _ z)
  have R5a := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q)
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app N) q r (q + r) rfl V
    (coefficientEvaluationSection l E W _ n V (w _ y))
    (coefficientEvaluationSection l E W _ n V (w _ z))
  rw [hθ, hθ] at R5a
  have R5b := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P)
    ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).map
        (Prod.mkHom ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q)
          ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app N))) p (q + r) k hk' V
    (coefficientEvaluationSection l E W _ n V (w _ x))
    (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) _ _ q r (q + r) rfl V
      (coefficientEvaluationSection l E W _ n V (w _ y))
      (coefficientEvaluationSection l E W _ n V (w _ z)))
  rw [hθ] at R5b
  have c2 := R3b.trans (congrArg (fun v ↦ coefficientTensorGenerator.{u, t + 1, t}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n) _
      (((M.tensor ⋙ coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj N)
      i r k hik V v (coefficientEvaluationSection l E W (M.tensor.obj (N.X r)) n V (w _ z))) R3a)
  have c4 := R5b.trans (congrArg (fun v ↦ coefficientTensorGenerator.{u, t + 1, t}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)
      (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) _
      p (q + r) k hk' V (u _ x) v) R5a)
  have c1 := (congrArg (fun v ↦ ((((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom
      (coefficientScalarTensorIso l E W n P Q).hom
      (𝟙 (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj N)))).f k).val.app
        V v)) R1).trans R2
  have cL1 := L1.trans (congrArg (coefficientIntegralScalarUnitSection l E W n _ V) L2)
  have cL2 := (congrArg (fun v ↦ (((coefficientScalarTensorIso l E W n P
    ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (Q, N))).hom.f k).val.app V v))
    cL1).trans L3
  have cL := (congrArg (fun v ↦ ((((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom
      (𝟙 (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P))
      (coefficientScalarTensorIso l E W n Q N).hom)).f k).val.app V v)) cL2).trans L4
  let T := coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  let T' := coefficientTotalTensor.{u, t + 1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
  let Ev := (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)
  let K := M.quotient l E W
  let θ := NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)
  let e := coefficientEvaluationTensorIso l E W n
  let m3 := T.map (Prod.mkHom (T.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q))) (θ.inv.app N))
  let mΞ := T.map (Prod.mkHom (e (K.obj P) (K.obj Q)).inv (𝟙 (Ev.obj (K.obj N)))) ≫
    (e (T'.obj (K.obj P, K.obj Q)) (K.obj N)).inv ≫ Ev.map b'.hom ≫
    (e (K.obj P) (T'.obj (K.obj Q, K.obj N))).hom ≫
    T.map (Prod.mkHom (𝟙 (Ev.obj (K.obj P))) (e (K.obj Q) (K.obj N)).hom)
  let m9 := T.map (Prod.mkHom (θ.hom.app P) (T.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N))))
  have cR := (congrArg (fun v ↦ (m9.f k).val.app V ((mΞ.f k).val.app V ((m3.f k).val.app V v)))
    c1).trans ((congrArg (fun v ↦ (m9.f k).val.app V ((mΞ.f k).val.app V v)) c2).trans
      ((congrArg (fun v ↦ (m9.f k).val.app V v) R4).trans c4))
  exact cL.trans cR.symm

end OrdinaryQuotient

end WeilConjectures
