/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitTensorSystemData
public import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralUnitCoherence
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorCoherentConstruction
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralUnitExistence

/-! # Reduction of the uniquely coherent integral unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField Padic
  HasDerivedCategory.standard
  WeilConjectures.pullbackTensorIntegralReductionTensor
  WeilConjectures.pullbackTensorIntegralReductionPullback
  WeilConjectures.pullbackTensorIntegralUnitReduction
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
/-- Reduction of the selected integral unit is the coherent system unit arrow.
Source: Stacks 07A4 and 0941, reduction of the canonical unit equation.
(blueprint: lem-pur-completed-unit-coherent-system-normalization-reduction).
Apply the reduction square to the canonical integral tensor comparison and the
left and right unitor equations, then cancel the reduction counits. -/
theorem completedUnit_coherentReduction_compatibility {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    let V := pullbackTensorIntegralUnit l E Y
    let eY := pullbackTensorIntegralUnitReduction l E Y
    let eX := pullbackTensorIntegralUnitReduction l E X
    let εI := (pullbackTensorIntegralUnitCoherence l E f).exists.choose
    let εS := (pullbackTensorSystemComparison_unit l E f).choose
    (pullbackTensorCalculus l E X).reduction.map εI.hom.hom ≫ eX.hom =
      (pullbackTensorIntegralReductionPullback l E f V).hom ≫
        (pullbackTensorSequenceDerived l E f).map eY.hom ≫ εS.hom := by
  have := (coherentReduction_fullyFaithful l E X).1
  have := (coherentReduction_fullyFaithful l E X).2
  let R := coherentReduction l E Y
  let Q := coherentReduction l E X
  let F := constructibleIntegralPullback l E f
  let H := pullbackTensorSequenceDerived l E f
  let U := constructibleIntegralTensor l E Y
  let V := constructibleIntegralTensor l E X
  let J := (pullbackTensorCalculus l E Y).systemClosed.tensor
  let I := (pullbackTensorCalculus l E X).systemClosed.tensor
  let a := reduction_tensor l E Y
  let b := reduction_tensor l E X
  let p := reduction_pullback l E f
  let ν := pullbackTensorSystemComparison l E f
  let μ := canonicalIntegralPullbackTensor l E f
  let UY := pullbackTensorIntegralUnit l E Y
  let UX := pullbackTensorIntegralUnit l E X
  let eY := pullbackTensorIntegralUnitReduction l E Y
  let eX := pullbackTensorIntegralUnitReduction l E X
  let εS := (pullbackTensorSystemComparison_unit l E f).choose
  have hS := (pullbackTensorSystemComparison_unit l E f).choose_spec
  let ε : F.obj UY ≅ UX := Q.preimageIso
    (p.app UY ≪≫ H.mapIso eY ≪≫ εS ≪≫ eX.symm)
  have hε : Q.map ε.hom ≫ (eX ≪≫ εS.symm).hom =
      p.hom.app UY ≫ H.map eY.hom := by
    dsimp only [ε, Functor.preimageIso]
    rw [Functor.map_preimage]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id, Iso.app_hom]
  have hεlaws : ∀ M : sfIntegralConstructibleCategory l E Y,
        (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY)
          ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) M).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
            (Prod.mkHom ε.hom (𝟙 _)) ≫
          ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ X hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
        ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
          ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ Y hY) M).hom) ∧
        (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M
          ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY))).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
            (Prod.mkHom (𝟙 _) ε.hom) ≫
          ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ X hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
        ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
          ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ Y hY) M).hom) := by
    intro M
    constructor
    · let a₀ := a.app (UY, M) ≪≫ J.mapIso (Iso.prod eY (Iso.refl (R.obj M)))
      let b₀ := b.app (UX, F.obj M) ≪≫
        I.mapIso (Iso.prod (eX ≪≫ εS.symm) (p.app M))
      let δ := I.mapIso (Iso.prod εS (Iso.refl (H.obj (R.obj M)))) ≪≫
        (pullbackTensorCalculus l E X).systemClosed.monoidal.leftUnitor _
      have hs := reduced_square R Q F H p a₀ (Iso.refl (R.obj M)) b₀ (p.app M)
        (pullbackTensorIntegralLeftUnitor l E Y M)
        (pullbackTensorIntegralLeftUnitor l E X (F.obj M))
        ((pullbackTensorCalculus l E Y).systemClosed.monoidal.leftUnitor (R.obj M)) δ
        (μ UY M ≪≫ V.mapIso (Iso.prod ε (Iso.refl (F.obj M))))
        (Iso.refl (F.obj M)) (ν.app (_, R.obj M)) (Iso.refl (H.obj (R.obj M)))
      have h := hs ?_ ?_ ?_ ?_ ?_
      · simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
          Category.comp_id, Category.assoc] using h.symm
      · simpa only [a₀, a, reduction_tensor, R, coherentReduction, UY, eY, J,
          pullbackTensorIntegralLeftUnitor, Iso.trans_hom, Functor.mapIso_hom,
          Iso.prod_hom, Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc,
          Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
          NatIso.ofComponents_hom_app] using
          (pullbackTensorIntegralLeftUnitor_existsUnique l E Y M).exists.choose_spec
      · have hu : Q.map (pullbackTensorIntegralLeftUnitor l E X (F.obj M)).hom =
            b.hom.app (UX, F.obj M) ≫ I.map (Prod.mkHom eX.hom (𝟙 _)) ≫
              ((pullbackTensorCalculus l E X).systemClosed.monoidal.leftUnitor
                (Q.obj (F.obj M))).hom :=
          (pullbackTensorIntegralLeftUnitor_existsUnique l E X (F.obj M)).exists.choose_spec
        let := (pullbackTensorCalculus l E X).systemClosed.monoidal
        have hn : I.map (Prod.mkHom (𝟙 _) (p.hom.app M)) ≫
            ((pullbackTensorCalculus l E X).systemClosed.monoidal.leftUnitor
              (H.obj (R.obj M))).hom =
            ((pullbackTensorCalculus l E X).systemClosed.monoidal.leftUnitor
              (Q.obj (F.obj M))).hom ≫ p.hom.app M := by
          simpa only [I, Q, R, F, H, Functor.comp_obj, MonoidalCategory.tensor_obj,
            CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
            MonoidalCategory.id_tensorHom] using
            MonoidalCategory.leftUnitor_naturality (p.hom.app M)
        dsimp only [b₀, δ, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
          Iso.refl_hom, Iso.app_hom, Iso.symm_hom]
        rw [hu]
        simp only [Category.assoc]
        rw [← hn]
        simp only [← I.map_comp_assoc, prod_comp, Category.assoc, Category.id_comp,
          Category.comp_id, Iso.inv_hom_id, H, R, Functor.comp_obj, Iso.prod_hom,
          Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Iso.app_hom]
      · simpa only [a₀, b₀, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
          Iso.refl_hom, Iso.app_hom, Category.assoc] using
          conjugate_tensor_comparison R Q F H U V J I a b p ν μ
            (integralComparison_reduction l E f) UY M UX (F.obj M) _ (R.obj M)
            ε (Iso.refl _) (eX ≪≫ εS.symm) (p.app M) eY (Iso.refl _) hε
            (by simp)
      · simp
      · simpa only [δ, H, I, J, ν, Functor.comp_obj,
          Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
          Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc] using (hS (R.obj M)).1.symm
    · let a₀ := a.app (M, UY) ≪≫ J.mapIso (Iso.prod (Iso.refl (R.obj M)) eY)
      let b₀ := b.app (F.obj M, UX) ≪≫
        I.mapIso (Iso.prod (p.app M) (eX ≪≫ εS.symm))
      let δ := I.mapIso (Iso.prod (Iso.refl (H.obj (R.obj M))) εS) ≪≫
        (pullbackTensorCalculus l E X).systemClosed.monoidal.rightUnitor _
      have hs := reduced_square R Q F H p a₀ (Iso.refl (R.obj M)) b₀ (p.app M)
        (pullbackTensorIntegralRightUnitor l E Y M)
        (pullbackTensorIntegralRightUnitor l E X (F.obj M))
        ((pullbackTensorCalculus l E Y).systemClosed.monoidal.rightUnitor (R.obj M)) δ
        (μ M UY ≪≫ V.mapIso (Iso.prod (Iso.refl (F.obj M)) ε))
        (Iso.refl (F.obj M)) (ν.app (R.obj M, _)) (Iso.refl (H.obj (R.obj M)))
      have h := hs ?_ ?_ ?_ ?_ ?_
      · simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
          Category.comp_id, Category.assoc] using h.symm
      · simpa only [a₀, a, reduction_tensor, R, coherentReduction, UY, eY, J,
          pullbackTensorIntegralRightUnitor, Iso.trans_hom, Functor.mapIso_hom,
          Iso.prod_hom, Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc,
          Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
          NatIso.ofComponents_hom_app] using
          (pullbackTensorIntegralRightUnitor_existsUnique l E Y M).exists.choose_spec
      · have hu : Q.map (pullbackTensorIntegralRightUnitor l E X (F.obj M)).hom =
            b.hom.app (F.obj M, UX) ≫ I.map (Prod.mkHom (𝟙 _) eX.hom) ≫
              ((pullbackTensorCalculus l E X).systemClosed.monoidal.rightUnitor
                (Q.obj (F.obj M))).hom :=
          (pullbackTensorIntegralRightUnitor_existsUnique l E X (F.obj M)).exists.choose_spec
        let := (pullbackTensorCalculus l E X).systemClosed.monoidal
        have hn : I.map (Prod.mkHom (p.hom.app M) (𝟙 _)) ≫
            ((pullbackTensorCalculus l E X).systemClosed.monoidal.rightUnitor
              (H.obj (R.obj M))).hom =
            ((pullbackTensorCalculus l E X).systemClosed.monoidal.rightUnitor
              (Q.obj (F.obj M))).hom ≫ p.hom.app M := by
          simpa only [I, Q, R, F, H, Functor.comp_obj, MonoidalCategory.tensor_obj,
            CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
            MonoidalCategory.tensorHom_id] using
            MonoidalCategory.rightUnitor_naturality (p.hom.app M)
        dsimp only [b₀, δ, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
          Iso.refl_hom, Iso.app_hom, Iso.symm_hom]
        rw [hu]
        simp only [Category.assoc]
        rw [← hn]
        simp only [← I.map_comp_assoc, prod_comp, Category.assoc, Category.id_comp,
          Category.comp_id, Iso.inv_hom_id, H, R, Functor.comp_obj, Iso.prod_hom,
          Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Iso.app_hom]
      · simpa only [a₀, b₀, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
          Iso.refl_hom, Iso.app_hom, Category.assoc] using
          conjugate_tensor_comparison R Q F H U V J I a b p ν μ
            (integralComparison_reduction l E f) M UY (F.obj M) UX (R.obj M) _
            (Iso.refl _) ε (p.app M) (eX ≪≫ εS.symm) (Iso.refl _) eY
            (by simp) hε
      · simp
      · simpa only [δ, H, I, J, ν, Functor.comp_obj,
          Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
          Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc] using (hS (R.obj M)).2.symm
  have heq : ε = (pullbackTensorIntegralUnitCoherence l E f).exists.choose :=
    (pullbackTensorIntegralUnitCoherence l E f).unique hεlaws
      (pullbackTensorIntegralUnitCoherence l E f).exists.choose_spec
  dsimp only
  rw [← heq]
  change Q.map ε.hom ≫ eX.hom = p.hom.app UY ≫ H.map eY.hom ≫ εS.hom
  apply (cancel_mono εS.inv).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.app_hom] using hε

end WeilConjectures.CompletedUnitPullback
