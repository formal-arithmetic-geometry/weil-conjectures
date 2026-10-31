/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionStrictTensor
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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

import all WeilConjectures.AlgebraicGeometry.SemilinearTotalTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.SemilinearOrdinaryInverseSystemKFlat
import all WeilConjectures.AlgebraicGeometry.SemilinearSystemsExistence
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
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
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.SystemScalarGenerators
import WeilConjectures.CategoryTheory.SystemCoinducedAdjunction
import WeilConjectures.CategoryTheory.SystemScalarTensorSection
import all WeilConjectures.Algebra.Homology.RingedScalarTensorMonoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence

/-! # Descent of the specified strict reduction tensor comparison

Source: Stacks 07A4 and 0G7E; original node steps 1--5 and 8
(blueprint: lem-sp-reduction-tensor-comparison-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false


universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections
open CategoryTheory.MonoidalCategory
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Scalar K-flatness at each level detects K-flatness of the whole sequence system. -/
private theorem reduction_system_kflat (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D)
    (P : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj P) := by
  let B := fun n : ℕ ↦ (constantSheaf (Scheme.ProEt.topology T)
    CommRingCat.{u + 1}).obj (CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
  let τ := fun n : ℕ ↦ (constantSheaf (Scheme.ProEt.topology T)
    CommRingCat.{u + 1}).map (CommRingCat.ofHom
      (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
        ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
          ULift.ringEquiv.{u, u + 1}.toRingHom)))
  let G := spMonoidalOrdinary l E T D r
  let : G.Additive := by dsimp [G, spMonoidalOrdinary]; infer_instance
  have (n : ℕ) :
      (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B τ n).Additive :=
    evaluationAdditive.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B τ n
  have (n : ℕ) : PreservesFiniteLimits
      (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B τ n) :=
    evaluationLimits.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B τ n
  have (n : ℕ) : PreservesFiniteColimits
      (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B τ n) :=
    evaluationColimits.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B τ n
  have e (n : ℕ) : G ⋙ evaluation.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) B τ n ≅
        (D.scalar (spIntegralReductionScalar l E T r.coefficient n)).model.E := by
    rw [WeilConjectures.SemilinearSections.evaluation_sequence.{u + 1, u, u + 1}]
    let i : (spMonoidalTowerEquivalence l E T D).functor ⋙
        SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n ≅
          spCoefficientEvaluation l E T D.equivalence n :=
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft D.equivalence.functor
          (SheafOfModules.strictSystemSequenceEquivalence
            (spCoefficientCommRings l E T)).unitIso.symm)
        (SheafOfModules.systemEvaluation (spCoefficientCommRings l E T) n)
    exact Functor.isoWhiskerLeft r.ordinary i ≪≫ r.level n
  have hout (n : ℕ) : CochainComplex.IsKFlatIndependentCoefficients (R := B n)
      (((evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B τ n).mapHomologicalComplex
        (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj P)) := by
    let S := (D.scalar (spIntegralReductionScalar l E T r.coefficient n)).model
    have hk := SheafOfModules.changeOfRings_isKFlat_independentCoefficients
      (spIntegralReductionScalar l E T r.coefficient n) P S.E S.obj_eq S.map_eq hP
    let ec := (NatIso.mapHomologicalComplex (e n) (.up ℤ)).app P
    exact SheafOfModules.kFlat_iso_independent (B n) ec.symm hk
  let R := spMonoidalSystemRing l E T
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro Z hZ i
  apply (systemsComponentwise.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B τ _).2
  intro n
  have hn : (((evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B τ n).mapHomologicalComplex
        (.up ℤ)).obj Z).Acyclic := by
    intro j
    exact (hZ j).map (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B τ n)
  exact (hout n _ hn i).of_iso (WeilConjectures.evaluationTotalIso.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) B τ n Z
      ((G.mapHomologicalComplex (.up ℤ)).obj P)).symm

private theorem section_natural {V : Type (u + 1)} [Category.{u} V]
    (J : GrothendieckTopology V) [EssentiallySmall.{u + 1} V]
    (R : Sheaf J CommRingCat.{u + 1})
    {M M' N N' : SemilinearSections.Mod.{u + 1, u, u + 1} J R} (f : M ⟶ M') (g : N ⟶ N')
    (U : Vᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (f ⊗ₘ g).val.app U (tensorSection.{u + 1, u, u + 1} J R M N U x y) =
      tensorSection.{u + 1, u, u + 1} J R M' N' U (f.val.app U x) (g.val.app U y) := by
  with_unfolding_all exact SheafOfModules.pure_natural R f g U x y

private theorem section_assoc {V : Type (u + 1)} [Category.{u} V]
    (J : GrothendieckTopology V) [EssentiallySmall.{u + 1} V]
    (R : Sheaf J CommRingCat.{u + 1}) (M N P : SemilinearSections.Mod.{u + 1, u, u + 1} J R)
    (U : Vᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) (z : P.val.obj U) :
    (α_ M N P).hom.val.app U
      (tensorSection.{u + 1, u, u + 1} J R (M ⊗ N) P U
        (tensorSection.{u + 1, u, u + 1} J R M N U x y) z) =
      tensorSection.{u + 1, u, u + 1} J R M (N ⊗ P) U x
        (tensorSection.{u + 1, u, u + 1} J R N P U y z) := by
  with_unfolding_all exact SheafOfModules.pure_assoc R M N P U x y z

private theorem section_left_unit {V : Type (u + 1)} [Category.{u} V]
    (J : GrothendieckTopology V) [EssentiallySmall.{u + 1} V]
    (R : Sheaf J CommRingCat.{u + 1}) (M : SemilinearSections.Mod.{u + 1, u, u + 1} J R)
    (U : Vᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U) :
    (λ_ M).hom.val.app U (tensorSection.{u + 1, u, u + 1} J R _ M U a x) = a • x := by
  with_unfolding_all exact SheafOfModules.pure_left_unit R M U a x

private theorem section_right_unit {V : Type (u + 1)} [Category.{u} V]
    (J : GrothendieckTopology V) [EssentiallySmall.{u + 1} V]
    (R : Sheaf J CommRingCat.{u + 1}) (M : SemilinearSections.Mod.{u + 1, u, u + 1} J R)
    (U : Vᵒᵖ) (x : M.val.obj U) (a : R.obj.obj U) :
    (ρ_ M).hom.val.app U (tensorSection.{u + 1, u, u + 1} J R M _ U x a) = a • x := by
  with_unfolding_all exact SheafOfModules.pure_right_unit R M U x a

/-- The given level comparison after the strict-system/sequence-site equivalence. -/
private def reductionLevel (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (n : ℕ) :
    spMonoidalOrdinary l E T D r ⋙
      SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n ≅
        (D.scalar (spIntegralReductionScalar l E T r.coefficient n)).model.E :=
  Functor.isoWhiskerLeft r.ordinary
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft D.equivalence.functor
        (SheafOfModules.strictSystemSequenceEquivalence
          (spCoefficientCommRings l E T)).unitIso.symm)
      (SheafOfModules.systemEvaluation (spCoefficientCommRings l E T) n)) ≪≫ r.level n

private theorem reduction_map_generator (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {M N : spIntegralSectionModules l E T}
    (f : M ⟶ N) (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : ((spCoefficientCommRings l E T).obj (op n)).obj.obj U) (x : M.val.obj U) :
    ((spMonoidalOrdinary l E T D r).map f).val.app (op (n, U.unop))
      (spMonoidalGenerator l E T D r M n U a x) =
      spMonoidalGenerator l E T D r N n U a (f.val.app U x) := by
  have hn := (r.level n).inv.naturality f
  have hh := congrArg (fun k ↦ k.val.app U
    (SheafOfModules.systemModelTmul
      (D.scalar (spIntegralReductionScalar l E T r.coefficient n)).model M U a x)) hn
  change _ = _ at hh
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hh
  exact hh.symm.trans (congrArg (((r.level n).inv.app N).val.app U)
    (SheafOfModules.systemScalarModel_map_tmul
      (D.scalar (spIntegralReductionScalar l E T r.coefficient n)) f U a x))

/-- Scalar adjunction reduces equality to sheafified binary tensor generators. -/
private theorem reduction_tensor_ext (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (M N : spIntegralSectionModules l E T)
    (H : spMonoidalSystems l E T)
    (f g : (spMonoidalOrdinary l E T D r).obj (M ⊗ N) ⟶ H)
    (h : ∀ n U x y,
      f.val.app (op (n, U.unop)) (spMonoidalGenerator l E T D r _ n U 1
        (tensorSection.{u + 1, u, u + 1} _ _ M N U x y)) =
      g.val.app (op (n, U.unop)) (spMonoidalGenerator l E T D r _ n U 1
        (tensorSection.{u + 1, u, u + 1} _ _ M N U x y))) : f = g := by
  have hn (n : ℕ) :
      (SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n).map f =
      (SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n).map g := by
    apply (cancel_epi ((reductionLevel l E T D r n).inv.app (M ⊗ N))).1
    apply ((D.scalar (spIntegralReductionScalar l E T r.coefficient n)).ordinaryAdj.homEquiv
      _ _).injective
    apply SheafOfModules.tensor_ext (spIntegralSectionRing l E T) M N
    intro U x y
    simp only [Adjunction.homEquiv_unit, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply]
    let S := D.scalar (spIntegralReductionScalar l E T r.coefficient n)
    have hu := S.unit_normalized (M ⊗ N) U
      (tensorSection.{u + 1, u, u + 1} _ _ M N U x y)
    have hf := congrArg (fun v ↦ f.val.app (op (n, U.unop))
      (((r.level n).inv.app (M ⊗ N)).val.app U v)) hu
    have hg := congrArg (fun v ↦ g.val.app (op (n, U.unop))
      (((r.level n).inv.app (M ⊗ N)).val.app U v)) hu
    with_unfolding_all exact hf.trans ((h n U x y).trans hg.symm)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  rcases V with ⟨n,U⟩
  exact congrArg (fun k ↦ k.val.app (op U)) (hn n)

/-- The same reduction for three tensor generators, using the ternary universal property. -/
private theorem reduction_tensor3_ext (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (M N P : spIntegralSectionModules l E T)
    (H : spMonoidalSystems l E T)
    (f g : (spMonoidalOrdinary l E T D r).obj ((M ⊗ N) ⊗ P) ⟶ H)
    (h : ∀ n U x y z,
      f.val.app (op (n, U.unop)) (spMonoidalGenerator l E T D r _ n U 1
        (tensorSection.{u + 1, u, u + 1} _ _ (M ⊗ N) P U
          (tensorSection.{u + 1, u, u + 1} _ _ M N U x y) z)) =
      g.val.app (op (n, U.unop)) (spMonoidalGenerator l E T D r _ n U 1
        (tensorSection.{u + 1, u, u + 1} _ _ (M ⊗ N) P U
          (tensorSection.{u + 1, u, u + 1} _ _ M N U x y) z))) : f = g := by
  have hn (n : ℕ) :
      (SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n).map f =
      (SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n).map g := by
    apply (cancel_epi ((reductionLevel l E T D r n).inv.app ((M ⊗ N) ⊗ P))).1
    apply ((D.scalar (spIntegralReductionScalar l E T r.coefficient n)).ordinaryAdj.homEquiv
      _ _).injective
    apply SheafOfModules.tensorTriple_ext (spIntegralSectionRing l E T) M N P
    intro U x y z
    simp only [Adjunction.homEquiv_unit, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply]
    let S := D.scalar (spIntegralReductionScalar l E T r.coefficient n)
    have hu := S.unit_normalized ((M ⊗ N) ⊗ P) U
      (tensorSection.{u + 1, u, u + 1} _ _ (M ⊗ N) P U
        (tensorSection.{u + 1, u, u + 1} _ _ M N U x y) z)
    have hf := congrArg (fun v ↦ f.val.app (op (n, U.unop))
      (((r.level n).inv.app ((M ⊗ N) ⊗ P)).val.app U v)) hu
    have hg := congrArg (fun v ↦ g.val.app (op (n, U.unop))
      (((r.level n).inv.app ((M ⊗ N) ⊗ P)).val.app U v)) hu
    with_unfolding_all exact hf.trans ((h n U x y z).trans hg.symm)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  rcases V with ⟨n,U⟩
  exact congrArg (fun k ↦ k.val.app (op U)) (hn n)

private theorem reduction_tensor_natural (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (C : SpReductionStrictTensor l E T D r)
    {M M' N N' : spIntegralSectionModules l E T} (f : M ⟶ M') (g : N ⟶ N') :
    (spMonoidalOrdinary l E T D r).map (f ⊗ₘ g) ≫ (C.ordinary M' N').hom =
      (C.ordinary M N).hom ≫
        ((spMonoidalOrdinary l E T D r).map f ⊗ₘ
          (spMonoidalOrdinary l E T D r).map g) := by
  apply reduction_tensor_ext l E T D r M N
  intro n U x y
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    reduction_map_generator, section_natural, C.forward]

private theorem reduction_tensor_associativity (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (C : SpReductionStrictTensor l E T D r)
    (M N P : spIntegralSectionModules l E T) :
    (spMonoidalOrdinary l E T D r).map (α_ M N P).hom ≫
      (C.ordinary M (N ⊗ P)).hom ≫
        (𝟙 _ ⊗ₘ (C.ordinary N P).hom) =
      (C.ordinary (M ⊗ N) P).hom ≫ ((C.ordinary M N).hom ⊗ₘ 𝟙 _) ≫
        (α_ ((spMonoidalOrdinary l E T D r).obj M)
          ((spMonoidalOrdinary l E T D r).obj N)
          ((spMonoidalOrdinary l E T D r).obj P)).hom := by
  apply reduction_tensor3_ext l E T D r M N P
  intro n U x y z
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    reduction_map_generator, section_natural, section_assoc,
    C.forward, SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]

/-- The prescribed scalar extension of the coefficient unit, at one level. -/
private def reductionUnitLevel (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (n : ℕ) :
    (D.equivalence.functor.obj (r.ordinary.obj
      (𝟙_ (spIntegralSectionModules l E T)))).level n ≅
        𝟙_ (SheafOfModules.systemLevel.{u + 1, u, u + 1} (spCoefficientCommRings l E T) n) :=
  (r.level n).app _ ≪≫
    eqToIso ((D.scalar (spIntegralReductionScalar l E T r.coefficient n)).model.obj_eq _) ≪≫
      SheafOfModules.comparisonUnitIso (spIntegralReductionScalar l E T r.coefficient n)

private theorem reductionUnitLevel_inv (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : ((spCoefficientCommRings l E T).obj (op n)).obj.obj U) :
    (reductionUnitLevel l E T D r n).inv.val.app U a =
      spMonoidalGenerator l E T D r _ n U a (1 : (spIntegralSectionRing l E T).obj.obj U) := by
  change ((r.level n).inv.app _).val.app U
    ((eqToHom ((D.scalar
      (spIntegralReductionScalar l E T r.coefficient n)).model.obj_eq
        (𝟙_ (spIntegralSectionModules l E T))).symm).val.app U
      ((SheafOfModules.comparisonUnitIso
        (spIntegralReductionScalar l E T r.coefficient n)).inv.val.app U a)) = _
  let φ := spIntegralReductionScalar l E T r.coefficient n
  let O := 𝟙_ (spIntegralSectionModules l E T)
  let S := (D.scalar φ).model
  exact (congrArg (fun y ↦ ((r.level n).inv.app O).val.app U
    ((eqToHom (S.obj_eq O).symm).val.app U y))
      (SheafOfModules.unitBackward_tmul φ U a)).trans
        (congrArg (((r.level n).inv.app O).val.app U)
          (SequenceScalarConstruction.modelTmul_eq φ S O U a
            (1 : (spIntegralSectionRing l E T).obj.obj U)))

set_option maxHeartbeats 5000000 in
-- Kernel conversion checks the concrete coefficient units across the sequence equivalence.
/-- The level unit maps assemble by the transition formula for their inverse generators. -/
private def reductionUnit (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) :
    (spMonoidalOrdinary l E T D r).obj (𝟙_ (spIntegralSectionModules l E T)) ≅
      𝟙_ (spMonoidalSystems l E T) := by
  let e (V : (ℕ × T.ProEt)ᵒᵖ) :=
    (SheafOfModules.evaluation _ (op V.unop.2)).mapIso
      (reductionUnitLevel l E T D r V.unop.1).symm
  let ep : (𝟙_ (spMonoidalSystems l E T)).val ≅
      ((spMonoidalOrdinary l E T D r).obj
        (𝟙_ (spIntegralSectionModules l E T))).val :=
    PresheafOfModules.isoMk e (by
      intro V W f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change ((spCoefficientCommRings l E T).obj (op V.unop.1)).obj.obj
        (op V.unop.2) at a
      symm
      let O := 𝟙_ (spIntegralSectionModules l E T)
      let m := (D.equivalence.functor.obj (r.ordinary.obj O))
      let h := leOfHom f.unop.1
      let U := op V.unop.2
      let c := ((spCoefficientCommRings l E T).map f.unop.1.op).hom.app U a
      have ht := r.transition O h U a
        (1 : (spIntegralSectionRing l E T).obj.obj U)
      have hi := reductionUnitLevel_inv l E T D r V.unop.1 U a
      have hj := reductionUnitLevel_inv l E T D r W.unop.1 U c
      have hnat := PresheafOfModules.naturality_apply
        (reductionUnitLevel l E T D r W.unop.1).inv.val f.unop.2.op c
      exact (congrArg (fun y ↦ (m.level W.unop.1).val.map f.unop.2.op
        ((m.transition h).val.app U y)) hi).trans
          ((congrArg ((m.level W.unop.1).val.map f.unop.2.op) ht).trans
            ((congrArg ((m.level W.unop.1).val.map f.unop.2.op) hj.symm).trans hnat.symm)))
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso ep.symm

private theorem reduction_generator_smul (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (M : spIntegralSectionModules l E T)
    (n : ℕ) (U : T.ProEtᵒᵖ) (a : (spIntegralSectionRing l E T).obj.obj U)
    (x : M.val.obj U) :
    spMonoidalGenerator l E T D r M n U 1 (a • x) =
      (spIntegralReductionScalar l E T r.coefficient n).hom.app U a •
        spMonoidalGenerator l E T D r M n U 1 x := by
  let S := D.scalar (spIntegralReductionScalar l E T r.coefficient n)
  change ((r.level n).inv.app M).val.app U
    (SheafOfModules.systemModelTmul S.model M U 1 (a • x)) = _
  have hh : SheafOfModules.systemModelTmul S.model M U 1 (a • x) =
      (spIntegralReductionScalar l E T r.coefficient n).hom.app U a •
        SheafOfModules.systemModelTmul S.model M U 1 x := by
    rw [← S.unit_normalized, ← S.unit_normalized]
    exact ((S.ordinaryAdj.unit.app M).val.app U).hom.map_smul a x
  rw [hh]
  exact (((r.level n).inv.app M).val.app U).hom.map_smul _ _

set_option maxHeartbeats 5000000 in
-- The concrete coefficient unit and the assembled sequence unit have large normal forms.
private theorem reductionUnit_hom_generator (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : ((spCoefficientCommRings l E T).obj (op n)).obj.obj U)
    (x : (spIntegralSectionRing l E T).obj.obj U) :
    (reductionUnit l E T D r).hom.val.app (op (n, U.unop))
      (spMonoidalGenerator l E T D r _ n U a x) =
      a * (spIntegralReductionScalar l E T r.coefficient n).hom.app U x := by
  let S := D.scalar (spIntegralReductionScalar l E T r.coefficient n)
  let O := 𝟙_ (spIntegralSectionModules l E T)
  change (SheafOfModules.comparisonUnitIso
    (spIntegralReductionScalar l E T r.coefficient n)).hom.val.app U
      ((eqToHom (S.model.obj_eq O)).val.app U
        (((r.level n).hom.app O).val.app U
          (((r.level n).inv.app O).val.app U
            (SheafOfModules.systemModelTmul S.model O U a x)))) = _
  have hh := congrArg (fun f ↦ f.val.app U
    (SheafOfModules.systemModelTmul S.model O U a x)) ((r.level n).app O).inv_hom_id
  change (((r.level n).hom.app O).val.app U
    (((r.level n).inv.app O).val.app U
      (SheafOfModules.systemModelTmul S.model O U a x))) = _ at hh
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hh
  have ht := SequenceScalarConstruction.modelTmul_eq
    (spIntegralReductionScalar l E T r.coefficient n) S.model O U a x
  have ht' := congrArg (fun x ↦ (eqToHom (S.model.obj_eq O)).val.app U x) ht
  simp only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at ht'
  exact (congrArg (fun y ↦ (SheafOfModules.comparisonUnitIso
    (spIntegralReductionScalar l E T r.coefficient n)).hom.val.app U
      ((eqToHom (S.model.obj_eq O)).val.app U y)) hh).trans
        ((congrArg ((SheafOfModules.comparisonUnitIso
          (spIntegralReductionScalar l E T r.coefficient n)).hom.val.app U) ht'.symm).trans
            (SheafOfModules.unitForward_tmul _ U a x))

private theorem reduction_left_unit (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (C : SpReductionStrictTensor l E T D r)
    (M : spIntegralSectionModules l E T) :
    (spMonoidalOrdinary l E T D r).map (λ_ M).hom =
      (C.ordinary _ M).hom ≫ ((reductionUnit l E T D r).hom ⊗ₘ 𝟙 _) ≫
        (λ_ ((spMonoidalOrdinary l E T D r).obj M)).hom := by
  apply reduction_tensor_ext l E T D r _ M
  intro n U a x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    reduction_map_generator, section_natural, section_left_unit,
    C.forward, SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply,
    reductionUnit_hom_generator, one_mul, reduction_generator_smul]

private theorem reduction_right_unit (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (C : SpReductionStrictTensor l E T D r)
    (M : spIntegralSectionModules l E T) :
    (spMonoidalOrdinary l E T D r).map (ρ_ M).hom =
      (C.ordinary M _).hom ≫ (𝟙 _ ⊗ₘ (reductionUnit l E T D r).hom) ≫
        (ρ_ ((spMonoidalOrdinary l E T D r).obj M)).hom := by
  apply reduction_tensor_ext l E T D r M _
  intro n U x a
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    reduction_map_generator, section_natural, section_right_unit,
    C.forward, SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply,
    reductionUnit_hom_generator, one_mul, reduction_generator_smul]

/-- Generator identities supply the ordinary strong monoidal coherence. -/
private def reductionOrdinaryCore (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (C : SpReductionStrictTensor l E T D r) :
    (spMonoidalOrdinary l E T D r).CoreMonoidal :=
  Functor.CoreMonoidal.mk' (reductionUnit l E T D r).symm
    (fun M N ↦ (C.ordinary M N).symm)
    (by
      intro M M' f N
      with_unfolding_all simpa only [Iso.symm_inv,
        (spMonoidalOrdinary l E T D r).map_id, tensorHom_id] using
        (reduction_tensor_natural l E T D r C f (𝟙 N)).symm)
    (by
      intro N N' M f
      with_unfolding_all simpa only [Iso.symm_inv,
        (spMonoidalOrdinary l E T D r).map_id, id_tensorHom] using
        (reduction_tensor_natural l E T D r C (𝟙 M) f).symm)
    (by
      intro M N P
      with_unfolding_all simpa only [Iso.symm_inv, tensorHom_id, id_tensorHom] using
        (reduction_tensor_associativity l E T D r C M N P).symm)
    (by
      intro M
      apply (cancel_epi ((spMonoidalOrdinary l E T D r).map (λ_ M).hom)).1
      simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
        (spMonoidalOrdinary l E T D r).map_id, Category.id_comp]
      rw [reduction_left_unit l E T D r C M]
      simp only [Iso.symm_inv, Category.assoc, Iso.hom_inv_id, Category.comp_id, tensorHom_id])
    (by
      intro M
      apply (cancel_epi ((spMonoidalOrdinary l E T D r).map (ρ_ M).hom)).1
      simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
        (spMonoidalOrdinary l E T D r).map_id, Category.id_comp]
      rw [reduction_right_unit l E T D r C M]
      simp only [Iso.symm_inv, Category.assoc, Iso.hom_inv_id, Category.comp_id, id_tensorHom])

/-- Evaluated scalar left adjoints detect the colimit comparison isomorphisms. -/
private theorem reduction_coproducts (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (K : Type) :
    PreservesColimitsOfShape (Discrete K) (spMonoidalOrdinary l E T D r) := by
  let G := spMonoidalOrdinary l E T D r
  let B := spCoefficientCommRings l E T
  let ev := SheafOfModules.systemSequenceEvaluation B
  have hEv (n : ℕ) : PreservesColimitsOfSize.{0, 0} (ev n) := by
    let := (SheafOfModules.SequenceCoinduced.adjunction B n).isLeftAdjoint
    change PreservesColimitsOfSize.{0, 0}
      ((SheafOfModules.strictSystemSequenceEquivalence B).inverse ⋙
        SheafOfModules.systemEvaluation B n)
    infer_instance
  have hG (n : ℕ) : PreservesColimitsOfSize.{0, 0} (G ⋙ ev n) := by
    let := (D.scalar (spIntegralReductionScalar l E T r.coefficient n)).ordinaryAdj.isLeftAdjoint
    constructor
    intro I _
    exact preservesColimitsOfShape_of_natIso (reductionLevel l E T D r n).symm
  constructor
  intro X
  let f := colimit.post X G
  have he (n : ℕ) : IsIso ((ev n).map f) := by
    let := hEv n
    let := hG n
    have hh := colimit.post_post X G (ev n)
    have : IsIso (colimit.post (X ⋙ G) (ev n) ≫ (ev n).map f) := by
      rw [hh]
      infer_instance
    exact IsIso.of_isIso_comp_left (colimit.post (X ⋙ G) (ev n)) _
  have : IsIso f := by
    have : IsIso ((SheafOfModules.strictSystemSequenceEquivalence B).inverse.map f) :=
      (SheafOfModules.strictRingSystem_isIso_iff B _).2 he
    exact isIso_of_reflects_iso f (SheafOfModules.strictSystemSequenceEquivalence B).inverse
  exact preservesColimit_of_isIso_post G X

/-- Native signed-total tensor coherence has the prescribed chain tensorator. -/
private theorem reductionComplexCore (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (C : SpReductionStrictTensor l E T D r) :
    letI := CategoryTheory.ScalarMonoidalProof.complexMonoidal.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (spIntegralSectionRing l E T)
    letI := CategoryTheory.ScalarMonoidalProof.complexMonoidal.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology T)) (spMonoidalSystemRing l E T)
    ∃ m : ((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).CoreMonoidal,
      ∀ P Q, (m.μIso P Q).inv = C.chain.inv.app (P,Q) := by
  let := CategoryTheory.ScalarMonoidalProof.complexMonoidal.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (spIntegralSectionRing l E T)
  let := CategoryTheory.ScalarMonoidalProof.complexMonoidal.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T)) (spMonoidalSystemRing l E T)
  let G := spMonoidalOrdinary l E T D r
  let := (reductionOrdinaryCore l E T D r C).toMonoidal
  have (j : ℤ) : PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G :=
    reduction_coproducts l E T D r _
  let m := Functor.CoreMonoidal.ofLaxMonoidal (G.mapHomologicalComplex (.up ℤ))
  refine ⟨m, ?_⟩
  intro P Q
  have h : m.μIso P Q = C.chain.app (P,Q) := by
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hh := G.ιTensorObj_mapCochainComplexμIso_hom_f P Q p q n hpq
    with_unfolding_all exact hh.trans (C.summand P Q p q n hpq).symm
  exact congrArg Iso.inv h

/-- The actual counit remains invertible after the sequence-site equivalence. -/
private theorem reductionCounit_isIso (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (P : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) :
    IsIso ((spMonoidalCounit l E T D r).app P) := by
  let := D.hasDerived
  let := r.computes P hP
  dsimp only [spMonoidalCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- Two-variable K-flat localization with exactly the recorded counit square. -/
private theorem reductionTensorDescent
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (C : SpReductionStrictTensor l E T D r)
    (source : SpIntegralClosed l E T)
    (sourceModel : Models.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) source)
    (target : SpSystemClosed l E T)
    (targetModel : Models.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (spMonoidalSystemRing l E T) target)
    (hSystem : ∀ P : CochainComplex (spIntegralSectionModules l E T) ℤ,
      P.IsKFlatIndependentCoefficients →
      CochainComplex.IsKFlatIndependentCoefficients
        (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ μ : source.tensor ⋙ spMonoidalReduction l E T D r ≅
        ((spMonoidalReduction l E T D r).prod (spMonoidalReduction l E T D r)) ⋙
          target.tensor,
      ∀ (P Q : CochainComplex (spIntegralSectionModules l E T) ℤ)
        (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
        (spMonoidalReduction l E T D r).map
          (tensorModelIso.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
            (spIntegralSectionRing l E T) source sourceModel P Q hP hQ).hom ≫
          μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          target.tensor.map (Prod.mkHom ((spMonoidalCounit l E T D r).app P)
            ((spMonoidalCounit l E T D r).app Q)) =
        (spMonoidalCounit l E T D r).app ((spMonoidalIntegralTotal l E T).obj (P,Q)) ≫
          DerivedCategory.Q.map (C.chain.inv.app (P,Q)) ≫
          (tensorModelIso.{u + 1, u, u + 1}
            (coefficientSequenceTopology (Scheme.ProEt.topology T))
            (spMonoidalSystemRing l E T) target targetModel
            (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj P)
            (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj Q)
            (hSystem P hP) (hSystem Q hQ)).hom := by
  let A := spIntegralSectionModules l E T
  let B := spMonoidalSystems l E T
  let F := (spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)
  let PR : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
  let PS : ObjectProperty (CochainComplex B ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X),
        HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) (DerivedCategory B)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
  obtain ⟨μ, hμ, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q F (spMonoidalReduction l E T D r)
    (spMonoidalCounit l E T D r) PR PS hSystem ff'
    (spMonoidalIntegralTotal l E T) (spMonoidalSystemTotal l E T)
    source.tensor target.tensor sourceModel.comparison targetModel.comparison C.chain.symm
    (fun P hp ↦ reductionCounit_isIso l E T D r P hp)
    (fun P Q hp hq ↦ reductionCounit_isIso l E T D r _
      (coefficientTotalTensor_isKFlat.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) P Q hp hq))
  refine ⟨μ, ?_⟩
  exact hμ

/-- Descend a prescribed strict balancing comparison to the recorded reduction.
The source and target tensor models are inputs; the ordinary comparison and chain
isomorphism in the output are exactly the prescribed ones.
Source: Stacks 07A4, 0G7E, 03EL; original node steps 1--5 and 8
(blueprint: lem-sp-reduction-tensor-comparison-descent).

Proof: at every level the ordinary reduction is the specified scalar extension.
Scalar extension preserves K-flatness, and exact evaluation commutes with total tensor
and detects exactness of systems. Hence reduction preserves every K-flat complex.
The recorded counit is invertible on those complexes, including their total tensors.
Resolve source objects by K-flat complexes. Fully faithful whiskering along the
resolving localization and the specified chain comparison give a unique natural
tensor comparison with exactly the displayed counit square.

For coherence, test ordinary maps on the local scalar generators. The prescribed
forward formula gives naturality and associativity. The levelwise scalar unit
isomorphisms assemble to a system unit isomorphism using the recorded transition
formula. Scalar linearity gives the two unit equations. This constructs a strong
monoidal structure on ordinary reduction. Evaluation detects preservation of the
coproducts used in signed total tensors, so the native complex monoidal structure
exists; its summand formula identifies its tensorator with exactly C.chain.
Restrict to K-flat complexes, use the supplied normalized tensor-model coherence
on each side, and localize through the actual counit. The representative square
identifies the resulting tensorator with the inverse of the natural comparison. -/
theorem sp_reduction_tensor_comparison_descent (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (C : SpReductionStrictTensor l E T D r)
    (source : SpIntegralClosed l E T)
    (sourceModel : SemilinearSections.Models.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) source)
    (sourceSymmetry : @SymmetricCategory
      (DerivedCategory (spIntegralSectionModules l E T)) _ source.monoidal)
    (sourceCoherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology T) (spIntegralSectionRing l E T)
      source sourceModel sourceSymmetry)
    (target : SpSystemClosed l E T)
    (targetModel : SemilinearSections.Models.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (spMonoidalSystemRing l E T) target)
    (targetSymmetry : @SymmetricCategory
      (DerivedCategory (spMonoidalSystems l E T)) _ target.monoidal)
    (targetCoherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1, u + 2}
      (coefficientSequenceTopology (Scheme.ProEt.topology T)) (spMonoidalSystemRing l E T)
      target targetModel targetSymmetry) :
    ∃ (μ : source.tensor ⋙ spMonoidalReduction l E T D r ≅
        ((spMonoidalReduction l E T D r).prod (spMonoidalReduction l E T D r)) ⋙ target.tensor)
      (monoidal : @Functor.CoreMonoidal
        (DerivedCategory (spIntegralSectionModules l E T)) _ source.monoidal
        (DerivedCategory (spMonoidalSystems l E T)) _ target.monoidal
        (spMonoidalReduction l E T D r)),
      let W : SpReductionMonoidalData l E T D r := {
        source := source
        sourceModel := sourceModel
        target := target
        targetModel := targetModel
        sourceSymmetry := sourceSymmetry
        sourceCoherence := sourceCoherence
        targetSymmetry := targetSymmetry
        targetCoherence := targetCoherence
        μ := μ
        monoidal := monoidal
        ordinary := C.ordinary
        chain := C.chain }
      SpReductionMonoidalTensor l E T D r W ∧
        ∃ hSystem : SpReductionSystemKflat l E T D r W,
          SpReductionDerived l E T D r W hSystem := by
  classical
  let hk := reduction_system_kflat l E T D r
  obtain ⟨μ, hμ⟩ := reductionTensorDescent l E T D r C source sourceModel target targetModel hk
  let JS := Scheme.ProEt.topology T
  let JT := coefficientSequenceTopology JS
  let RS := spIntegralSectionRing l E T
  let RT := spMonoidalSystemRing l E T
  let := CategoryTheory.ScalarMonoidalProof.complexMonoidal.{u + 1, u, u + 1} JS RS
  let := CategoryTheory.ScalarMonoidalProof.complexMonoidal.{u + 1, u, u + 1} JT RT
  let := CategoryTheory.ScalarMonoidalProof.kFlatMonoidal.{u + 1, u, u + 1} JS RS
  let := CategoryTheory.ScalarMonoidalProof.kFlatMonoidal.{u + 1, u, u + 1} JT RT
  let := source.monoidal
  let := target.monoidal
  let F := (spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)
  obtain ⟨mF, hmF⟩ := reductionComplexCore l E T D r C
  let := mF.toMonoidal
  let K := coefficientKFlatInclusion.{u + 1, u + 1, u} JS RS
  let KT := coefficientKFlatInclusion.{u + 1, u + 1, u} JT RT
  let L := K ⋙ DerivedCategory.Q.{u + 2}
  let LT := KT ⋙ DerivedCategory.Q.{u + 2}
  let EF := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients (J := JT) (R := RT))
    (K ⋙ F) (fun P ↦ hk P.obj P.property)
  let : EF.Monoidal :=
    (CategoryTheory.ScalarMonoidalProof.restrictCore _ _ F mF hk).toMonoidal
  let : L.Monoidal :=
    (CategoryTheory.ScalarMonoidalProof.modelCore.{u + 1, u, u + 1, u + 2}
      (M := sourceModel) (β := sourceSymmetry) (h := sourceCoherence) JS RS source).toMonoidal
  let : LT.Monoidal :=
    (CategoryTheory.ScalarMonoidalProof.modelCore.{u + 1, u, u + 1, u + 2}
      (M := targetModel) (β := targetSymmetry) (h := targetCoherence) JT RT target).toMonoidal
  let W := (HomologicalComplex.quasiIso (spIntegralSectionModules l E T)
    (.up ℤ)).inverseImage K
  let : L.IsLocalization W :=
    RingedDerivedNative.kFlatLocalization.{u + 1, u, u + 1, u + 2} JS RS
  let e : L ⋙ spMonoidalReduction l E T D r ≅ EF ⋙ LT := NatIso.ofComponents
    (fun P ↦ by
      let := reductionCounit_isIso l E T D r P.obj P.property
      exact asIso ((spMonoidalCounit l E T D r).app P.obj))
    (fun f ↦ by
      exact (spMonoidalCounit l E T D r).naturality f.hom)
  have hn := CategoryTheory.ScalarMonoidalProof.normalizedDescent L W
    (spMonoidalReduction l E T D r) (EF ⋙ LT) e μ
  obtain ⟨monoidal, hm⟩ := hn (by
    intro P Q
    have hh := hμ P.obj Q.obj P.property Q.property
    with_unfolding_all change (
      (spMonoidalReduction l E T D r).map
        (sourceModel.iso JS RS source P.obj Q.obj P.property Q.property).hom ≫
          μ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
            ((spMonoidalCounit l E T D r).app P.obj ⊗ₘ
              (spMonoidalCounit l E T D r).app Q.obj) =
      (spMonoidalCounit l E T D r).app
        ((coefficientTotalTensor.{u + 1, u + 1, u} JS RS).obj (P.obj,Q.obj)) ≫
        (DerivedCategory.Q.map ((mF.μIso P.obj Q.obj).inv) ≫
          (targetModel.iso JT RT target _ _ (hk P.obj P.property) (hk Q.obj Q.property)).hom))
    rw [hmF]
    with_unfolding_all exact hh)
  refine ⟨μ, monoidal, ?_⟩
  dsimp only
  refine ⟨hm, (fun P hP _ ↦ hk P hP), ?_⟩
  intro P Q hP hQ fP fQ
  exact hμ P Q hP hQ

end AlgebraicGeometry.ProEtale
