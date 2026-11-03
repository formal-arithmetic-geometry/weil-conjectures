/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionDescentSystem
public import WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionRepresentativeModels
import all WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionRepresentativeModels
import WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionRepresentativeAssembly
import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexUnaryModel
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedComparisonData

/-! # The reduction tensor square on good representatives

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: lem-pod-reduction-good-representative-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance 1000000] SheafOfModules.instAbelian

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh CoefficientClosedStructure.tensor
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors
  pullbackTensorReductionModel pullbackTensorSystemModel
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.IsFlatOnSite
  derivedInternalHomOfUniverses coefficientSequenceCommRingSheaf
  pullbackTensorSequenceInverse integralComparisonSequencePullback
  pullbackTensorSystemComparison PodReductionRepresentatives.systemChain
attribute [local implicit_reducible] CategoryTheory.uniformProd
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralReductionTargetHasDerivedCategory coefficientFiniteHasDerived
  coefficientIntegralInternalHom coefficientSequenceInternalHom coefficientFiniteInternalHom
  podReindexCalculus pullbackTensorCalculus
  integralTowerHasDerivedCategory coefficientSequenceHasDerived
  pullbackTensorSequenceDerived
  integralComparisonDerivedSequencePullback

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open PodReductionRepresentatives

set_option quotPrecheck false in
set_option hygiene false in
local notation "R[" W "]" =>
  (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "I[" g "]" =>
  (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "F[" g "]" => podReindexingComplexFunctor l E g none
set_option quotPrecheck false in
set_option hygiene false in
local notation "T[" W "]" => PodReindexingCoherence.total l E W none
set_option quotPrecheck false in
set_option hygiene false in
local notation "S[" W "]" => coefficientTotalTensor.{u, u + 1, u}
  (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)

attribute [local instance 10000000] HasDerivedCategory.standard
attribute [local irreducible] podOrdinaryReindex PodReductionRepresentatives.factor
set_option allowUnsafeReducibility true in
attribute [local irreducible] podReindexingDerivedFunctor podReindexingDerivedFactors
open PodReindexingCoherence

private theorem tensorMap_comp
    {C D : Type*} [Category* C] [Category* D] (T : C × C ⥤ D)
    {A B C' A' B' C'' : C} (f : A ⟶ B) (g : A' ⟶ B')
    (h : B ⟶ C') (i : B' ⟶ C'') :
    T.map (Prod.mkHom f g) ≫ T.map (Prod.mkHom h i) =
      T.map (Prod.mkHom (f ≫ h) (g ≫ i)) := by
  rw [← T.map_comp]
  rfl

private theorem paste_tensor_square
    {D : Type*} [Category* D] (T : D × D ⥤ D)
    {A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ D₀ D₁ D₂ : D}
    (a : B₀ ≅ A₀) (b : B₀ ≅ C₀) (c : C₀ ≅ D₀)
    (a₁ : B₁ ≅ A₁) (a₂ : B₂ ≅ A₂)
    (b₁ : B₁ ≅ C₁) (b₂ : B₂ ≅ C₂)
    (c₁ : C₁ ≅ D₁) (c₂ : C₂ ≅ D₂)
    (tA : A₀ ⟶ T.obj (A₁, A₂)) (tB : B₀ ⟶ T.obj (B₁, B₂))
    (tC : C₀ ⟶ T.obj (C₁, C₂)) (tD : D₀ ⟶ T.obj (D₁, D₂))
    (ha : a.hom ≫ tA = tB ≫ T.map (Prod.mkHom a₁.hom a₂.hom))
    (hb : b.hom ≫ tC = tB ≫ T.map (Prod.mkHom b₁.hom b₂.hom))
    (hc : c.hom ≫ tD = tC ≫ T.map (Prod.mkHom c₁.hom c₂.hom)) :
    tA ≫ T.map (Prod.mkHom (a₁.symm ≪≫ b₁ ≪≫ c₁).hom
        (a₂.symm ≪≫ b₂ ≪≫ c₂).hom) =
      (a.symm ≪≫ b ≪≫ c).hom ≫ tD := by
  apply (cancel_epi a.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% ha, tensorMap_comp]
  simp only [Iso.hom_inv_id_assoc]
  rw [← tensorMap_comp, ← reassoc_of% hb, ← hc]

/-- The specified coefficient/pullback exchange preserves the tensor comparison.
The four ringed sites may be the condensed coefficient sheaves on two schemes before
and after coefficient extension. No special presentation of the coefficient ring is
required. In particular the result applies to reduction and to the Frobenius
inverse image, including its semilinear structural ring map.

The statement holds on the entire unbounded derived categories, hence on the images
of flat-term K-flat representatives without any further descent or completeness
hypothesis. The comparison is the specified composite, not an arbitrary isomorphism.

Source: latest blueprint, prop-pod-dual-tate-data-compatibility, Step 5, using the
composition and 2-isomorphism clauses of lem-sfb-ringed-derived-monoidal-comparisons.
Proof: paste the tensor equations for the first composition, the given geometric
2-isomorphism, and the second composition. Functoriality of the target tensor combines
the two component maps. Cancel the first composition isomorphism on the tensor and
on each factor. These are the same model-isomorphism cancellations as in the
representative proof, now for the current ringed-topos comparisons.
(blueprint: lem-pod-reduction-good-representative-square). -/
theorem podReduction_representative_square
    {X Y Z W : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z}
    {a : Morphism X W} {b : Morphism W Z}
    {k h : Morphism X Z}
    {lf : Lift f} {lg : Lift g} {la : Lift a} {lb : Lift b}
    {lk : Lift k} {lh : Lift h}
    {θ : k.inverse ≅ g.inverse ⋙ f.inverse}
    {ψ : h.inverse ≅ b.inverse ⋙ a.inverse} {η : k.inverse ≅ h.inverse}
    (c : Composition lf lg lk θ) (d : Composition la lb lh ψ)
    (e : TwoIso lk lh η) (U V : Z.D) :
    let δ := c.pullback.symm ≪≫ e.pullback ≪≫ d.pullback
    lf.edge.left.map (lg.tensor U V).hom ≫
        (lf.tensor (lg.edge.left.obj U) (lg.edge.left.obj V)).hom ≫
        X.closed.tensor.map (Prod.mkHom (δ.hom.app U) (δ.hom.app V)) =
      δ.hom.app (Z.closed.tensor.obj (U, V)) ≫
        la.edge.left.map (lb.tensor U V).hom ≫
        (la.tensor (lb.edge.left.obj U) (lb.edge.left.obj V)).hom := by
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app, Category.assoc] using
    paste_tensor_square X.closed.tensor
      (c.pullback.app (Z.closed.tensor.obj (U, V)))
      (e.pullback.app (Z.closed.tensor.obj (U, V)))
      (d.pullback.app (Z.closed.tensor.obj (U, V)))
      (c.pullback.app U) (c.pullback.app V)
      (e.pullback.app U) (e.pullback.app V)
      (d.pullback.app U) (d.pullback.app V)
      (lf.edge.left.map (lg.tensor U V).hom ≫
        (lf.tensor (lg.edge.left.obj U) (lg.edge.left.obj V)).hom)
      (lk.tensor U V).hom (lh.tensor U V).hom
      (la.edge.left.map (lb.tensor U V).hom ≫
        (la.tensor (lb.edge.left.obj U) (lb.edge.left.obj V)).hom)
      (c.tensor U V) (e.tensor U V) (d.tensor U V)

end WeilConjectures
