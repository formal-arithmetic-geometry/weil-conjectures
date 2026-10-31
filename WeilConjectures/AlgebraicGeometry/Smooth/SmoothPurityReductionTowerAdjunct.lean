/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement


/-! # Invertibility of the specified reduction adjuncts

Source: blueprint latest, normalized-towers-reduction, normalization paragraph;
Stacks Tags 06YY, 0G7E.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

private theorem isIso_app_of_iso
    {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (τ : F ⟶ G) {K L : C} (e : K ≅ L)
    [IsIso (τ.app K)] : IsIso (τ.app L) := by
  exact IsIso.of_isIso_fac_left (τ.naturality e.hom)

private theorem opSequence_map_comp
    {C D : Type*} [Category* C] [Category* D]
    {X : ℕ → C} (f : ∀ n, X (n + 1) ⟶ X n) (G : C ⥤ D)
    {m n : ℕ} (h : m ≤ n) :
    G.map ((Functor.ofOpSequence f).map (homOfLE h).op) =
      (Functor.ofOpSequence (X := fun i ↦ G.obj (X i))
        (fun i ↦ G.map (f i))).map (homOfLE h).op := by
  let a : Functor.ofOpSequence f ⋙ G ⟶
      Functor.ofOpSequence (X := fun i ↦ G.obj (X i)) (fun i ↦ G.map (f i)) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro i
      simp only [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp])
  simpa only [Functor.comp_map, a, NatTrans.ofOpSequence_app,
    Category.comp_id, Category.id_comp] using a.naturality (homOfLE h).op

section ScalarAdjunct
universe c v r
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S V : Sheaf J CommRingCat.{r}} {a : R ⟶ S} {b : S ⟶ V} {d : R ⟶ V}

private theorem scalar_adjunct_isIso (hd : d = a ≫ b)
    (A : SystemScalarModel a) (B : SystemScalarModel b) (D : SystemScalarModel d)
    (X : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
    (N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J V))
    (en : N ≅ A.model.E.obj X) (em : M ≅ D.model.E.obj X)
    (t : N ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).map b)).obj M)
    (ht : ∀ U x,
      em.hom.val.app U (t.val.app U
        (en.inv.val.app U (systemModelTmul A.model X U 1 x))) =
      systemModelTmul D.model X U 1 x) :
    IsIso ((B.ordinaryAdj.homEquiv N M).symm t) := by
  let f := (B.ordinaryAdj.homEquiv N M).symm t
  let e := systemScalarModelComposition hd A B D
  have he : B.model.E.map en.inv ≫ f ≫ em.hom = e.hom.app X := by
    apply (B.ordinaryAdj.homEquiv _ _).injective
    rw [B.ordinaryAdj.homEquiv_naturality_left,
      B.ordinaryAdj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    apply systemScalarModel_hom_ext A X _
    intro U x
    change em.hom.val.app U (t.val.app U
      (en.inv.val.app U (systemModelTmul A.model X U 1 x))) = _
    rw [ht]
    have hh := systemScalarModel_transpose_tmul B _ _ (e.hom.app X) U 1
      (systemModelTmul A.model X U 1 x)
    rw [one_smul] at hh
    calc
      _ = (e.hom.app X).val.app U
          (systemModelTmul B.model (A.model.E.obj X) U 1
            (systemModelTmul A.model X U 1 x)) := by
        simpa only [e, map_one, mul_one] using
          (systemScalarModelComposition_tmul hd A B D X U 1 1 x).symm
      _ = _ := hh
  have : IsIso (B.model.E.map en.inv ≫ f ≫ em.hom) := by
    rw [he]
    infer_instance
  have : IsIso (f ≫ em.hom) := IsIso.of_isIso_comp_left (B.model.E.map en.inv) _
  exact IsIso.of_isIso_comp_right f em.hom

private theorem kflat_of_iso
    {P Q : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R)) ℤ}
    (e : P ≅ Q) (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R) Q := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro F hF
  let e' := ((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso e
  have hh := hP F hF
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hh ⊢
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso
    ((HomotopyCategory.quotient _ _).mapIso e') hh

end ScalarAdjunct

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

private theorem coefficient_map_eq {m n : ℕ} (h : m ≤ n) :
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((spCoefficientCommRings l E T).map (homOfLE h).op) =
      (spCoefficientRings l E T).map (homOfLE h).op := by
  unfold spCoefficientCommRings spCoefficientRings spCoefficientReduction
  exact opSequence_map_comp _ _ h

private theorem reduction_scalar_comp
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    {m n : ℕ} (h : m ≤ n) :
    spIntegralReductionScalar l E T coefficient m =
      spIntegralReductionScalar l E T coefficient n ≫
        (spCoefficientCommRings l E T).map (homOfLE h).op := by
  apply (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
  simp only [spIntegralReductionScalar, Functor.map_comp, Category.assoc]
  congr 1
  simp only [spIntegralEllProjection, Functor.map_preimage, Category.assoc]
  rw [coefficient_map_eq]
  rw [limit.w]

set_option maxHeartbeats 800000 in
-- Kernel checking the extracted ordinary reduction helper exceeds the default budget.
private theorem ordinary_reduction_isIso
    (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T)
    [ordinary.Additive]
    (level : spReductionOrdinaryLevels l E T D coefficient ordinary)
    (transition : IsSpReductionTransition l E T D coefficient ordinary level)
    {m n : ℕ} (h : m ≤ n) :
    ∀ X : spIntegralSectionModules l E T,
      IsIso ((D.ordinaryReduction h).app (ordinary.obj X)) := by
  let := D.hasDerived
  let := D.equivalenceAdditive
  let := D.evaluationLimits n
  let := D.evaluationColimits n
  let := D.evaluationLimits m
  let := D.evaluationColimits m
  intro X
  rw [D.ordinaryReduction_eq]
  apply scalar_adjunct_isIso (reduction_scalar_comp l E T coefficient h)
    (D.scalar _) (D.scalar _) (D.scalar _) X _ _
    ((level n).app X) ((level m).app X)
  intro U x
  have ht := transition X h U 1 x
  simp only [map_one] at ht
  have he := congrArg (fun y ↦ ((level m).hom.app X).val.app U y) ht
  simp only [spStrictTransitionSection, spReductionGenerator] at he
  change ((level m).hom.app X).val.app U
    (((D.equivalence.functor.obj (ordinary.obj X)).transition h).val.app U
      (((level n).inv.app X).val.app U
        (systemModelTmul (D.scalar
          (spIntegralReductionScalar l E T coefficient n)).model X U 1 x))) = _
  simpa only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, (level m).inv_hom_id_app,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using he

set_option maxHeartbeats 800000 in
-- Kernel checking the concrete coefficient-sheaf comparisons exceeds the default budget.
set_option linter.unusedVariables false in
-- The fixed interface includes universal and evaluation; this proof only needs computes.
/-- The actual reduction morphisms supplied by D are invertible on strict derived
reduction. This is a compatibility assertion about D.reduction, not just existence
of unrelated isomorphisms between successive scalar extensions.

Source: blueprint latest, sec-smooth-purity, normalized-towers-reduction, normalization;
Stacks Tags 06YY and 0G7E
(blueprint: lem-sp-reduction-tower-adjunct-normalization).

Proof:
1. Resolve an arbitrary integral complex by a flat-term K-flat complex P. The counit
identifies its image under red with the degreewise strict tensor reduction of P.
2. For m <= n, D.reduction_rep describes the reduction on this representative as
derived scalar extension followed by the ordinary tensor adjunct of its transition.
The assumed pure-tensor transition formula and D.ordinaryReduction_eq identify that
ordinary adjunct with (x tensor c) tensor d mapping to x tensor quotient(c)*d.
Equality on pure tensors determines the sheafified tensor map.
3. Successive derived quotient normalization identifies this map with the canonical
invertible transitivity comparison. Its inverse inserts one in the middle factor.
The normalization of the scalar-extension units is precisely the adjunct relation
of step 2. Scalar-model uniqueness transports this computation to D.scalar's models.
4. Use the evaluation comparisons and the computation counits to conjugate this
isomorphism to D.reduction on red(Q P). Naturality conjugates it along a K-flat
representative isomorphism to red(M), proving the assertion for every M.
Equal indices use the tensor unitor, and three-index compatibility follows from
associativity of scalar multiplication. No qcqs, boundedness, flat coefficient map,
or constructibility assumption is used. The zero complex and empty site are included.
-/
theorem sp_reduction_tower_adjunct_normalization
    (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T)
    [ordinary.Additive]
    (level : spReductionOrdinaryLevels l E T D coefficient ordinary)
    (transition : IsSpReductionTransition l E T D coefficient ordinary level)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D)
    (counit : DerivedCategory.Q ⋙ red ⟶
      ordinary.mapHomologicalComplex (.up ℤ) ⋙ spTowerLocalization l E T D)
    (universal : red.IsLeftDerivedFunctor counit
      (HomologicalComplex.quasiIso (spIntegralSectionModules l E T) (.up ℤ)))
    (computes : ∀ P : CochainComplex (spIntegralSectionModules l E T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) P →
        IsIso (counit.app P))
    (evaluation : spReductionDerivedEvaluations l E T D coefficient red) :
    ∀ M : DerivedCategory (spIntegralSectionModules l E T),
      IsSpNormalizedTower l E T D (red.obj M) := by
  clear universal evaluation
  let := D.hasDerived
  let := D.equivalenceAdditive
  intro M m n h
  let := D.evaluationLimits n
  let := D.evaluationColimits n
  let := D.evaluationLimits m
  let := D.evaluationColimits m
  let evn := spCoefficientEvaluation l E T D.equivalence n
  let evm := spCoefficientEvaluation l E T D.equivalence m
  have : evn.Additive := Functor.additive_of_preserves_binary_products _
  have : evm.Additive := Functor.additive_of_preserves_binary_products _
  have hOrd := ordinary_reduction_isIso l E T D coefficient ordinary level transition h
  let G := DerivedCategory.Q.objPreimage M
  let eG : DerivedCategory.Q.obj G ≅ M := DerivedCategory.Q.objObjPreimageIso M
  obtain ⟨P, f, hP, _hflat, hf, _hepi⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := spIntegralSectionRing l E T) G
  let := hf
  have hLevel : CochainComplex.IsKFlatIndependentCoefficients
      (R := (spCoefficientCommRings l E T).obj (op n))
      ((evn.mapHomologicalComplex (.up ℤ)).obj
        ((ordinary.mapHomologicalComplex (.up ℤ)).obj P)) := by
    let A := (D.scalar (spIntegralReductionScalar l E T coefficient n)).model
    have hp := changeOfRings_isKFlat_independentCoefficients
      (spIntegralReductionScalar l E T coefficient n) P A.E A.obj_eq A.map_eq hP
    exact kflat_of_iso.{u + 1, u, u + 1}
      ((Functor.mapHomologicalComplexCompIso (level n) (.up ℤ)).app P).symm hp
  let QP := (ordinary.mapHomologicalComplex (.up ℤ)).obj P
  have hChain : IsIso
      ((NatTrans.mapHomologicalComplex (D.ordinaryReduction h) (.up ℤ)).app QP) := by
    have hi : ∀ i : ℤ, IsIso
        (((NatTrans.mapHomologicalComplex (D.ordinaryReduction h) (.up ℤ)).app QP).f i) := by
      intro i
      exact hOrd (P.X i)
    exact HomologicalComplex.Hom.isIso_of_components _
  have := (D.scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)).model.computes
    _ hLevel
  have : IsIso ((D.reduction h).app ((spTowerLocalization l E T D).obj QP)) := by
    rw [D.reduction_rep h QP]
    infer_instance
  have := computes P hP
  let eP : red.obj (DerivedCategory.Q.obj P) ≅
      (spTowerLocalization l E T D).obj QP := asIso (counit.app P)
  have := isIso_app_of_iso (D.reduction h) eP.symm
  exact isIso_app_of_iso (D.reduction h)
    (red.mapIso (asIso (DerivedCategory.Q.map f) ≪≫ eG))

end AlgebraicGeometry.ProEtale
