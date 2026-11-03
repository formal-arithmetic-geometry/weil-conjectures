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
import all WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionDescentSystem
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReindexingReductionTensorData
import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexUnaryModel
import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexStrictTensor
import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictDerivedSquare
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SixFunctors.Coefficient.CoefficientReductionTensorEvaluationPasting
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedComparisonData

/-! # Pasting the reduction tensor square on specified representatives

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: lem-pod-reduction-representative-assembly)
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

private theorem map_three {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {P Q R S Q' R' : C}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S}
    {d : P ⟶ Q'} {e : Q' ⟶ R'} {f : R' ⟶ S}
    (h : a ≫ b ≫ c = d ≫ e ≫ f) :
    F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e ≫ F.map f := by
  simpa only [Functor.map_comp] using congrArg (fun z ↦ F.map z) h

/-- Assemble the tensor square from its normalized representative diagrams.
This categorical lemma applies to the condensed derived categories with
coefficients pulled back from a condensed ring, including non-flat coefficient change.
No equality is inferred from finite reductions: the strict square `hc` is used directly.

Source: latest blueprint prop-pod-dual-tate-data-compatibility, Step 5.
Proof: precompose with the image of the source tensor-model isomorphism and
postcompose with the tensor of the target model isomorphisms. Naturality and the
three unary normalization squares rewrite the two composites to the two sides of
`hc`. Whisker that strict equality and cancel the two isomorphisms.
(blueprint: lem-pod-reduction-representative-assembly). -/
theorem podReduction_assemble_representative
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (R : C ⥤ A) (S : D ⥤ B) (F : C ⥤ D) (G : A ⥤ B)
    (T : C × C ⥤ C) (W : D × D ⥤ D)
    (U : A × A ⥤ A) (V : B × B ⥤ B)
    (a : R ⋙ G ⟶ F ⋙ S) (v : T ⋙ F ⟶ F.prod F ⋙ W)
    (w : U ⋙ G ⟶ G.prod G ⋙ V)
    (τY : T ⋙ R ⟶ R.prod R ⋙ U) (τX : W ⋙ S ⟶ S.prod S ⋙ V)
    (P Q T₀ : C) (PX QX FT TX : D)
    (bY : T₀ ≅ T.obj (P, Q)) (bX : TX ≅ W.obj (PX, QX))
    (fP : F.obj P ≅ PX) (fQ : F.obj Q ≅ QX) (fT : F.obj T₀ ≅ FT)
    (RP RQ RT SY : A) (IP IQ IT IS SI RFP RFQ RFT RTX SX : B)
    (rP : R.obj P ≅ RP) (rQ : R.obj Q ≅ RQ) (rT : R.obj T₀ ≅ RT)
    (rFP : S.obj PX ≅ RFP) (rFQ : S.obj QX ≅ RFQ)
    (rFT : S.obj FT ≅ RFT) (rTX : S.obj TX ≅ RTX)
    (sY : SY ≅ U.obj (RP, RQ)) (sI : SI ≅ V.obj (IP, IQ))
    (sX : SX ≅ V.obj (RFP, RFQ))
    (iP : G.obj RP ⟶ IP) (iQ : G.obj RQ ⟶ IQ)
    (iT : G.obj RT ⟶ IT) (iS : G.obj SY ⟶ IS)
    (ψY : RT ⟶ SY) (IψY : IT ⟶ IS) (systemt : IS ⟶ SI)
    (βP : IP ⟶ RFP) (βQ : IQ ⟶ RFQ) (βT : IT ⟶ RFT)
    (tensorβ : SI ⟶ SX) (t : FT ⟶ TX) (Rt : RFT ⟶ RTX) (ψX : RTX ⟶ SX)
    (hUP : G.map rP.hom ≫ iP ≫ βP = a.app P ≫ S.map fP.hom ≫ rFP.hom)
    (hUQ : G.map rQ.hom ≫ iQ ≫ βQ = a.app Q ≫ S.map fQ.hom ≫ rFQ.hom)
    (hUT : G.map rT.hom ≫ iT ≫ βT = a.app T₀ ≫ S.map fT.hom ≫ rFT.hom)
    (hY : R.map bY.hom ≫ τY.app (P, Q) ≫ U.map (Prod.mkHom rP.hom rQ.hom) =
      rT.hom ≫ ψY ≫ sY.hom)
    (hX : S.map bX.hom ≫ τX.app (PX, QX) ≫ V.map (Prod.mkHom rFP.hom rFQ.hom) =
      rTX.hom ≫ ψX ≫ sX.hom)
    (hO : F.map bY.hom ≫ v.app (P, Q) ≫ W.map (Prod.mkHom fP.hom fQ.hom) =
      fT.hom ≫ t ≫ bX.hom)
    (hS : G.map sY.hom ≫ w.app (RP, RQ) ≫ V.map (Prod.mkHom iP iQ) =
      iS ≫ systemt ≫ sI.hom)
    (hN : tensorβ ≫ sX.hom = sI.hom ≫ V.map (Prod.mkHom βP βQ))
    (hi : G.map ψY ≫ iS = iT ≫ IψY)
    (hr : S.map t ≫ rTX.hom = rFT.hom ≫ Rt)
    (hc : IψY ≫ systemt ≫ tensorβ = βT ≫ Rt ≫ ψX) :
    G.map (τY.app (P, Q)) ≫ w.app (R.obj P, R.obj Q) ≫
      V.map (Prod.mkHom (a.app P) (a.app Q)) =
    a.app (T.obj (P, Q)) ≫ S.map (v.app (P, Q)) ≫
      τX.app (F.obj P, F.obj Q) := by
  have hw := w.naturality (Prod.mkHom rP.hom rQ.hom)
  have ha := a.naturality bY.hom
  have hd := τX.naturality (Prod.mkHom fP.hom fQ.hom)
  dsimp only [Functor.comp_map, Functor.prod_map] at hw ha hd
  let pre := G.map (R.map bY.hom)
  let post := V.map (Prod.mkHom (S.map fP.hom ≫ rFP.hom)
    (S.map fQ.hom ≫ rFQ.hom))
  have : IsIso post := tensor_isIso V (S.mapIso fP ≪≫ rFP) (S.mapIso fQ ≪≫ rFQ)
  apply (cancel_epi pre).1
  apply (cancel_mono post).1
  have hL : pre ≫ G.map (τY.app (P, Q)) ≫ w.app (R.obj P, R.obj Q) ≫
        V.map (Prod.mkHom (a.app P) (a.app Q)) ≫ post =
      G.map rT.hom ≫ iT ≫ IψY ≫ systemt ≫ tensorβ ≫ sX.hom := by
    dsimp only [pre, post]
    conv_lhs =>
      rhs; rhs; rhs
      rw [tensor_comp]
    rw [← hUP, ← hUQ]
    rw [← tensor_comp V (G.map rP.hom) (G.map rQ.hom) (iP ≫ βP) (iQ ≫ βQ)]
    rw [← reassoc_of% hw, ← G.map_comp_assoc, ← G.map_comp_assoc]
    simp only [Category.assoc]
    rw [hY]
    simp only [Functor.map_comp, Category.assoc]
    rw [← tensor_comp V iP iQ βP βQ]
    rw [reassoc_of% hS, reassoc_of% hi, ← hN]
  have hR : pre ≫ a.app (T.obj (P, Q)) ≫ S.map (v.app (P, Q)) ≫
        τX.app (F.obj P, F.obj Q) ≫ post =
      G.map rT.hom ≫ iT ≫ βT ≫ Rt ≫ ψX ≫ sX.hom := by
    dsimp only [pre, post]
    rw [← tensor_comp V (S.map fP.hom) (S.map fQ.hom) rFP.hom rFQ.hom]
    rw [← reassoc_of% hd, reassoc_of% ha]
    rw [← S.map_comp_assoc, ← S.map_comp_assoc]
    simp only [Category.assoc]
    rw [hO]
    simp only [Functor.map_comp, Category.assoc]
    rw [hX, reassoc_of% hr, ← reassoc_of% hUT]
  have hc' := congrArg (fun z ↦ G.map rT.hom ≫ iT ≫ z ≫ sX.hom) hc
  simp only [Category.assoc] at hc'
  simpa only [Category.assoc] using hL.trans (hc'.trans hR.symm)

private theorem path_tensor
    {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ C) (V : D × D ⥤ D)
    (L F R H : C ⥤ D) (cl : L ≅ F) (e : L ≅ R) (cr : R ≅ H)
    (P Q : C)
    (dl : L.obj (T.obj (P, Q)) ⟶ V.obj (L.obj P, L.obj Q))
    (df : F.obj (T.obj (P, Q)) ⟶ V.obj (F.obj P, F.obj Q))
    (dr : R.obj (T.obj (P, Q)) ⟶ V.obj (R.obj P, R.obj Q))
    (dh : H.obj (T.obj (P, Q)) ⟶ V.obj (H.obj P, H.obj Q))
    (hl : cl.hom.app (T.obj (P, Q)) ≫ df =
      dl ≫ V.map (Prod.mkHom (cl.hom.app P) (cl.hom.app Q)))
    (he : e.hom.app (T.obj (P, Q)) ≫ dr =
      dl ≫ V.map (Prod.mkHom (e.hom.app P) (e.hom.app Q)))
    (hr : cr.hom.app (T.obj (P, Q)) ≫ dh =
      dr ≫ V.map (Prod.mkHom (cr.hom.app P) (cr.hom.app Q))) :
    let a := cl.symm ≪≫ e ≪≫ cr
    df ≫ V.map (Prod.mkHom (a.hom.app P) (a.hom.app Q)) =
      a.hom.app (T.obj (P, Q)) ≫ dh := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  apply (cancel_epi (cl.hom.app (T.obj (P, Q)))).1
  simp only [Category.assoc]
  rw [reassoc_of% hl, tensor_comp]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← tensor_comp V (e.hom.app P) (e.hom.app Q)
    (cr.hom.app P) (cr.hom.app Q)]
  rw [← reassoc_of% he, ← hr]

/-- The tensor square for two ring-compatible paths of derived pullback.
For coefficient change and geometric Frobenius these are the two paths around the
condensed scalar/pullback square. The path comparisons retain their K-flat
normalizations; no coefficient flatness or boundedness hypothesis is needed.

Source: latest blueprint prop-pod-dual-tate-data-compatibility, Step 5, using
lem-sfb-ringed-derived-monoidal-comparisons, compositor and 2-isomorphism clauses.
Proof: precompose with the first compositor, apply its tensor equation, then the
2-isomorphism tensor equation, then the second compositor tensor equation. The
unary path comparisons telescope. Cancel the first compositor.
(blueprint: lem-pod-reduction-ringed-path-tensor-square). -/
theorem podReduction_ringed_path_tensor_square
    {X Y A D : Site.{u, w}}
    {f : Morphism X A} {g : Morphism A Y}
    {h : Morphism X D} {k : Morphism D Y}
    {left right : Morphism X Y}
    (lf : Lift f) (lg : Lift g) (lh : Lift h) (lk : Lift k)
    (ll : Lift left) (lr : Lift right)
    {θl : left.inverse ≅ g.inverse ⋙ f.inverse}
    {θr : right.inverse ≅ k.inverse ⋙ h.inverse}
    {θ : left.inverse ≅ right.inverse}
    (cl : Composition lf lg ll θl) (cr : Composition lh lk lr θr)
    (e : TwoIso ll lr θ) (P Q : Y.D) :
    let a := cl.pullback.symm ≪≫ e.pullback ≪≫ cr.pullback
    lf.edge.left.map (lg.tensor P Q).hom ≫
        (lf.tensor (lg.edge.left.obj P) (lg.edge.left.obj Q)).hom ≫
        X.closed.tensor.map (Prod.mkHom (a.hom.app P) (a.hom.app Q)) =
      a.hom.app (Y.closed.tensor.obj (P, Q)) ≫
        lh.edge.left.map (lk.tensor P Q).hom ≫
        (lh.tensor (lk.edge.left.obj P) (lk.edge.left.obj Q)).hom := by
  simpa only [Category.assoc] using
    WeilConjectures.path_tensor Y.closed.tensor X.closed.tensor
    ll.edge.left (lg.edge.left ⋙ lf.edge.left) lr.edge.left
    (lk.edge.left ⋙ lh.edge.left) cl.pullback e.pullback cr.pullback P Q
    (ll.tensor P Q).hom
    (lf.edge.left.map (lg.tensor P Q).hom ≫
      (lf.tensor (lg.edge.left.obj P) (lg.edge.left.obj Q)).hom)
    (lr.tensor P Q).hom
    (lh.edge.left.map (lk.tensor P Q).hom ≫
      (lh.tensor (lk.edge.left.obj P) (lk.edge.left.obj Q)).hom)
    (cl.tensor P Q) (e.tensor P Q) (cr.tensor P Q)

end WeilConjectures
