/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionReductionData
import WeilConjectures.SixFunctors.Integral.IntegralReductionShiftedHomFiniteQcqs
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Milnor

/-! # Joint faithfulness of reductions on constructible integral objects

Source: the Milnor mapping-limit proof of integralConstructibleReductionHom.
(blueprint: lem-sf-integral-reductions-jointly-faithful).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry
namespace WeilConjectures

private theorem reduction_roos_isHomotopyLimit
    {A : Type*} [Category A] [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {F : ℕᵒᵖ ⥤ A} (c : Cone F) [HasProduct (fun n ↦ F.obj (op n))]
    (δ : (∏ᶜ fun n ↦ F.obj (op n)) ⟶ c.pt⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle (fun n ↦ F.map (homOfLE n.le_succ).op)
      c.pt (Pi.lift (fun n ↦ c.π.app (op n))) δ) : IsHomotopyLimit c := by
  refine ⟨_, productIsProduct _, δ, ?_⟩
  have h₁ : Fan.IsLimit.lift (productIsProduct (fun n ↦ F.obj (op n)))
      (fun n ↦ c.π.app (op n)) = Pi.lift (fun n ↦ c.π.app (op n)) := by
    apply Pi.hom_ext
    intro n
    exact (Fan.IsLimit.fac _ _ n).trans
      (Pi.lift_π (fun n ↦ c.π.app (op n)) n).symm
  have h₂ : towerShift (F := F) (productIsProduct (fun n ↦ F.obj (op n))) =
      towerProductShift (fun n ↦ F.map (homOfLE n.le_succ).op) := by
    apply Pi.hom_ext
    intro n
    simp only [towerShift, towerProductShift, Pi.lift_π]
    exact Fan.IsLimit.fac _ _ n
  rw [h₁, h₂]
  exact h

/-- Equality of actual integral morphisms follows from equality of all their finite
reductions on this constructible domain. This uses the finite shifted-Hom theorem and
the Milnor injection, rather than any faithfulness assumption about derived evaluation.

Source: lem-coef-integral-finite-extension, mapping-limit proof, and Bhatt--Scholze 3.5.7.
(blueprint: lem-sf-integral-reductions-jointly-faithful).

Proof: the defining Roos triangle of the target makes its reduction cone a homotopy limit.
The shifted Hom groups into the terms are finite by the qcqs finiteness theorem, so the
Milnor map is bijective. Equal reductions have equal composites with every adjunction
unit by naturality. Thus their images under the Milnor map agree; injectivity and the
faithful full-subcategory inclusion give equality. -/
theorem integral_reductions_jointly_faithful
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) (X : SixFunctorSpace D)
    {K M : sfIntegralConstructibleCategory C.l E X.obj.left} (a b : K ⟶ M)
    (h : ∀ m : ℕ, (IntegralProjectionReduction.reduction d m X).map a =
      (IntegralProjectionReduction.reduction d m X).map b) : a = b := by
  obtain ⟨hp, δ, hδ⟩ := M.property.1
  let := hp
  have hc : IsHomotopyLimit (sfIntegralReductionCone C.l E X.obj.left M.obj) := by
    apply reduction_roos_isHomotopyLimit (δ := δ)
    change IsDerivedLimitTriangle
      (K := fun m ↦ (sfDerivedReductionRestricted C.l E X.obj.left m).obj M.obj)
      (fun m ↦ (sfIntegralReductionTower C.l E X.obj.left M.obj).map
        (homOfLE m.le_succ).op)
      M.obj (Pi.lift (fun m ↦ (sfDerivedReductionUnit C.l E X.obj.left m).app M.obj)) δ
    simpa only [sfIntegralReductionTower,
      Functor.ofOpSequence_map_homOfLE_succ] using hδ
  have (m : ℕ) : Finite
      (K.obj⟦(1 : ℤ)⟧ ⟶ (sfIntegralReductionTower C.l E X.obj.left M.obj).obj (op m)) :=
    integralReduction_shiftedHom_finite_qcqs D C.l C.different E X K M m
  apply (sfIntegralConstructible C.l E X.obj.left).ι.map_injective
  apply (hc.bijective_milnorMap K.obj).injective
  apply Subtype.ext
  funext m
  change a.hom ≫ (sfDerivedReductionUnit C.l E X.obj.left m).app M.obj =
    b.hom ≫ (sfDerivedReductionUnit C.l E X.obj.left m).app M.obj
  have he : (scalarReductionDerivedExtension C.l E X.obj.left m).map a.hom =
      (scalarReductionDerivedExtension C.l E X.obj.left m).map b.hom :=
    congrArg (fun z ↦ z.hom) (h m)
  have hu := (sfDerivedReductionUnit C.l E X.obj.left m).naturality a.hom
  have hv := (sfDerivedReductionUnit C.l E X.obj.left m).naturality b.hom
  dsimp only [Functor.id_map, Functor.comp_map] at hu hv
  rw [hu, hv]
  exact congrArg (fun z ↦
    (sfDerivedReductionUnit C.l E X.obj.left m).app K.obj ≫
      (scalarReductionDerivedRestriction C.l E X.obj.left m).map z) he

end WeilConjectures
