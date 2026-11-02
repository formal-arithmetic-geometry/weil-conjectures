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

universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

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
        (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq V x y)) =
      coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
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
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj
        ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q), N)) ⟶ Y)
    (h : ∀ (p q r i k : ℤ) (hpq : p + q = i) (hik : i + r = k) (V : W.ProEtᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) (z : (N.X r).val.obj V),
      (f.f k).val.app V (coefficientIntegralScalarUnitSection l E W n _ V
        (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) _ N i r k hik V
          (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W) P Q p q i hpq V x y) z)) =
      (g.f k).val.app V (coefficientIntegralScalarUnitSection l E W n _ V
        (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) _ N i r k hik V
          (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W) P Q p q i hpq V x y) z))) :
    f = g := by
  let adj := (coefficientOrdinaryScalarAdjunction l E W n).mapHomologicalComplex (.up ℤ)
  apply (adj.homEquiv _ _).injective
  apply CategoryTheory.tensorGenerator_ext₃.{t+1, t, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) P Q N
  intro p q r i k hpq hik V x y z
  exact h p q r i k hpq hik V x y z

/-- An isomorphism of complexes of module sheaves is inverse to its inverse on sections.
Source: Stacks 03CZ. -/
theorem cochainIso_hom_inv_section
    {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {P Q : CochainComplex (SheafOfModules.{w} R) ℤ} (e : P ≅ Q) (k : ℤ) (U : Cᵒᵖ)
    (y : (Q.X k).val.obj U) : (e.hom.f k).val.app U ((e.inv.f k).val.app U y) = y :=
  congrArg (fun z : Q ⟶ Q ↦ (z.f k).val.app U y) e.inv_hom_id

/-- An isomorphism of complexes of module sheaves is inverse to its inverse on sections.
Source: Stacks 03CZ. -/
theorem cochainIso_inv_hom_section
    {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {P Q : CochainComplex (SheafOfModules.{w} R) ℤ} (e : P ≅ Q) (k : ℤ) (U : Cᵒᵖ)
    (x : (P.X k).val.obj U) : (e.inv.f k).val.app U ((e.hom.f k).val.app U x) = x :=
  congrArg (fun z : P ⟶ P ↦ (z.f k).val.app U x) e.hom_inv_id

namespace OrdinaryQuotient

/-- A total associator of strict systems, evaluated and transported along isomorphisms of
the finite evaluations, reassociates finite tensor generators.
Source: Stacks 03EK, 07A4, 0941. -/
theorem transportedAssociator_generator (n : ℕ)
    (X Y Z : CochainComplex (coefficientSequenceModules l E W) ℤ)
    {A B C : CochainComplex (normalizedDVRModules l E W n) ℤ}
    (α : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj X ≅ A)
    (β : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Y ≅ B)
    (γ : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Z ≅ C)
    (b' : (coefficientTotalTensor.{u, t+1, t} (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((coefficientTotalTensor.{u, t+1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (X, Y), Z) ≅
      (coefficientTotalTensor.{u, t+1, t} (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        (X, (coefficientTotalTensor.{u, t+1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (Y, Z)))
    (hb' : CoefficientComplexAssociatorFormula
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) X Y Z b')
    (p q r pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + r = qr) (hk : pq + r = k)
    (hk' : p + qr = k) (U : W.ProEtᵒᵖ)
    (x : (A.X p).val.obj U) (y : (B.X q).val.obj U) (z : (C.X r).val.obj U) :
    (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom
          ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom α.inv β.inv) ≫
            (coefficientEvaluationTensorIso l E W n X Y).inv) γ.inv) ≫
      (coefficientEvaluationTensorIso l E W n _ Z).inv ≫
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map b'.hom ≫
      (coefficientEvaluationTensorIso l E W n X _).hom ≫
      (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom α.hom
          ((coefficientEvaluationTensorIso l E W n Y Z).hom ≫
            (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
              (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom β.hom γ.hom)))).f k).val.app U
      (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) _ _ pq r k hk U
        (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n) _ _ p q pq hpq U x y) z) =
    coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) _ _ p qr k hk' U x
      (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) _ _ q r qr hqr U y z) := by
  obtain ⟨x0, hx0⟩ := coefficientEvaluationSection_surjective l E W (X.X p) n U
    ((α.inv.f p).val.app U x)
  obtain ⟨y0, hy0⟩ := coefficientEvaluationSection_surjective l E W (Y.X q) n U
    ((β.inv.f q).val.app U y)
  obtain ⟨z0, hz0⟩ := coefficientEvaluationSection_surjective l E W (Z.X r) n U
    ((γ.inv.f r).val.app U z)
  have hx : x = (α.hom.f p).val.app U (coefficientEvaluationSection l E W (X.X p) n U x0) := by
    rw [hx0]
    exact (congrArg (fun φ ↦ (φ.f p).val.app U x) α.inv_hom_id).symm
  sorry

end OrdinaryQuotient

end WeilConjectures
