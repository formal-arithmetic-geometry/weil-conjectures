/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.CategoryTheory.AlgebraDiagramEvaluationAdjunctionNormalizationDefs
import all Sheaf.CategoryTheory.AlgebraDiagramComparisonTools
import all Sheaf.CategoryTheory.DiagramRingRestrictionPushforward
import Sheaf.CategoryTheory.AlgebraDiagramDerivedComparisonCoherence

/-! # Evaluation and the derived adjunction of an algebra diagram

Source: Stacks 07A6 and 0D6E
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.AlgebraDiagramAdjunctionPresentation

attribute [local instance 100000] eAX_additive eAY_additive eAX_limits eAY_limits
  eAX_colimits eAY_colimits

attribute [local instance 100000] evaluationRingCompose evaluationAddCompose evaluationSheafify
  evaluationLocallyBijective cacheKinj cacheSheafLimits cacheSheafColimits
  algebraDiagramModules_abelian


private theorem coefficientAcyclic
    {E F : Type u} [SmallCategory E] [SmallCategory F]
    {T : GrothendieckTopology E} {V : GrothendieckTopology F}
    (R S : Sheaf T RingCat.{u}) (P : Sheaf V RingCat.{u})
    (hR : ∀ U (a b : R.obj.obj U), a * b = b * a)
    (hS : ∀ U (a b : S.obj.obj U), a * b = b * a)
    (hP : ∀ U (a b : P.obj.obj U), a * b = b * a)
    (a : R ⟶ S) (g : RingedToposMorphism R P)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} P)]
    (I : CochainComplex (ringedSiteModules.{u} S) ℤ) (hI : I.IsKInjective) :
    IsIso (g.modules.rightDerivedFunctorUnitQ
      (((SheafOfModules.restrictScalars.{u} a).mapHomologicalComplex (.up ℤ)).obj I)) := by
  obtain ⟨RG, eta, hRG, _, hacyc⟩ := CategoryTheory.coefficientAcyclicDerived R S P hR hS hP a g
  exact diagramUnit_isIso_of_other g.modules RG eta hRG _ (hacyc I hI)

attribute [local irreducible] algebraDiagramConstantRing Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.mapDerivedCategoryCompIso

variable {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D} {A : CommRingCat.{u}}
    (p : AlgebraDiagramAdjunctionPresentation J C D K L A)
variable [HasDerivedCategory.{w} (ringedSiteModules.{u} p.BX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} p.BY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} p.AX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} p.AY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramConstantRing K A))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramConstantRing L A))]
    [∀ j : J, HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramRingAt p.BX j))]
    [∀ j : J, HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramRingAt p.BY j))]

omit [HasDerivedCategory.{w} (ringedSiteModules.{u} p.BY)] in
private theorem varying_evaluation_acyclic
    [∀ j : J, (p.eAX j).Additive] [∀ j : J, (p.eAY j).Additive]
    [∀ j : J, PreservesFiniteLimits (p.eAX j)]
    [∀ j : J, PreservesFiniteLimits (p.eAY j)]
    [∀ j : J, PreservesFiniteColimits (p.eAX j)]
    [∀ j : J, PreservesFiniteColimits (p.eAY j)] (j : J)
    (c : p.fA.modules ⋙ p.eAY j ≅ p.eAX j ⋙ p.s.modules)
    (d : p.PA ⋙ (p.eAY j).mapDerivedCategory ≅ (p.eAX j).mapDerivedCategory ⋙ p.P)
    (hd : AlgebraDiagramDerivedSquareNormalized p.fA.modules p.s.modules
      (p.eAX j) (p.eAY j) c d)
    (cj : (p.fj j).modules ⋙ p.rYj j ≅ p.rXj j ⋙ p.s.modules)
    (dj : p.Pj j ⋙ (p.rYj j).mapDerivedCategory ≅ (p.rXj j).mapDerivedCategory ⋙ p.P)
    (hdj : AlgebraDiagramDerivedSquareNormalized (p.fj j).modules p.s.modules
      (p.rXj j) (p.rYj j) cj dj)
    (I : CochainComplex (ringedSiteModules.{u} p.BX) ℤ) [I.IsKInjective] :
    IsIso ((p.fj j).modules.rightDerivedFunctorUnitQ
      (((p.eBX j).mapHomologicalComplex (.up ℤ)).obj I)) := by
  have hI := coefficientAcyclic p.AX p.BX p.AY
    (fun U ↦ diagramConstantRing_comm K A (Opposite.op U.unop.2)) p.commX
    (fun U ↦ diagramConstantRing_comm L A (Opposite.op U.unop.2)) p.aX p.fA I inferInstance
  have hunit : IsIso (p.fA.modules.rightDerivedFunctorUnitQ
      ((p.rX.mapHomologicalComplex (.up ℤ)).obj I)) := hI
  have hmap : IsIso ((p.eAY j).mapDerivedCategory.map
      (p.fA.modules.rightDerivedFunctorUnitQ
        ((p.rX.mapHomologicalComplex (.up ℤ)).obj I))) := by
    let := hunit
    infer_instance
  have hA := (diagramSquare_unit_iff p.fA.modules p.s.modules (p.eAX j) (p.eAY j)
    c d hd ((p.rX.mapHomologicalComplex (.up ℤ)).obj I)).mp hmap
  have hAj : IsIso (p.s.modules.rightDerivedFunctorUnitQ
      (((p.rXj j).mapHomologicalComplex (.up ℤ)).obj
        (((p.eBX j).mapHomologicalComplex (.up ℤ)).obj I))) := hA
  have hj := (diagramSquare_unit_iff (p.fj j).modules p.s.modules (p.rXj j) (p.rYj j)
    cj dj hdj (((p.eBX j).mapHomologicalComplex (.up ℤ)).obj I)).mpr hAj
  let := CategoryTheory.restriction_reflects (algebraDiagramCoefficientAt p.aY j)
  let := diagramExactDerived_reflectsIso (p.rYj j)
  exact isIso_of_reflects_iso _ (p.rYj j).mapDerivedCategory
/-- The normalized comparisons preserve counits, transposes and coefficients.
Source: Stacks 07A6 and 0D6E
(blueprint: lem-pur-algebra-diagram-evaluation-adjunction-normalization).

Proof: construct ordinary comparisons, derive them by acyclicity, and apply the
unit-normalized counit and naturality equations to the ordinary coefficient cube
and the actual diagram transitions. Constant evaluation preserves K-injectives;
conservative scalar restriction detects the required varying evaluation acyclicity. -/
theorem evaluationAdjunctionNormalization : p.EvaluationAdjunctionNormalization := by
  classical
  have : ∀ j : J, (p.eAX j).Additive := p.eAX_additive
  have : ∀ j : J, (p.eAY j).Additive := p.eAY_additive
  have : ∀ j : J, PreservesFiniteLimits (p.eAX j) := p.eAX_limits
  have : ∀ j : J, PreservesFiniteLimits (p.eAY j) := p.eAY_limits
  have : ∀ j : J, PreservesFiniteColimits (p.eAX j) := p.eAX_colimits
  have : ∀ j : J, PreservesFiniteColimits (p.eAY j) := p.eAY_colimits
  let : ∀ j : J, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (algebraDiagramRingAt p.AX j)) :=
    fun j ↦ algebraDiagramConstantDerivedAt (algebraDiagramConstantRing K A) j
  let : ∀ j : J, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (algebraDiagramRingAt p.AY j)) :=
    fun j ↦ algebraDiagramConstantDerivedAt (algebraDiagramConstantRing L A) j
  obtain ⟨o⟩ := p.ordinaryComparisons_exists
  obtain ⟨d, hd⟩ := diagramRestrictionDerived
    (fun U ↦ diagramConstantRing_comm K A (op U.unop.2)) p.commX
    (fun U ↦ diagramConstantRing_comm L A (op U.unop.2)) p.aX p.aY p.fB p.fA o.c
  choose dj hdj using fun j ↦ diagramRestrictionDerived
    (diagramConstantRing_comm K A) (fun U ↦ p.commX (op (op j, U.unop)))
    (diagramConstantRing_comm L A) (algebraDiagramCoefficientAt p.aX j)
    (algebraDiagramCoefficientAt p.aY j) (p.fj j) p.s (o.cj j)
  choose delta hdelta using fun j ↦
    (algebraDiagramNormalizedDerivedSquare p.fA.modules p.s.modules
      (p.eAX j) (p.eAY j) (fun I hI ↦ by
        have := diagramConstantEvaluation_kinjective K (algebraDiagramConstantRing K A) j I hI
        rw [Functor.rightDerivedFunctorUnitQ_eq]
        infer_instance) (o.cA j)).exists
  choose beta hbeta using fun j ↦
    (algebraDiagramNormalizedDerivedSquare p.fB.modules (p.fj j).modules
      (p.eBX j) (p.eBY j) (fun I hI ↦ by
        let := hI
        exact varying_evaluation_acyclic p j (o.cA j) (delta j) (hdelta j)
          (o.cj j) (dj j) (hdj j) I) (o.cB j)).exists
  have hB (j k : J) (a : j ⟶ k) := diagramRestrictionDerived
    (fun U ↦ p.commX (op (op j, U.unop)))
    (fun U ↦ p.commX (op (op k, U.unop)))
    (fun U ↦ p.commY (op (op j, U.unop)))
    (algebraDiagramRingArrow p.BX a) (algebraDiagramRingArrow p.BY a)
    (p.fj k) (p.fj j) (o.caB a)
  choose qaB hqaB using hB
  have hA (j k : J) (a : j ⟶ k) := diagramRestrictionDerived
    (diagramConstantRing_comm K A) (diagramConstantRing_comm K A)
    (diagramConstantRing_comm L A)
    (algebraDiagramRingArrow p.AX a) (algebraDiagramRingArrow p.AY a)
    p.s p.s (o.caA a)
  choose qaA hqaA using hA
  have hc := p.derivedComparisonCoherence o d beta delta dj
    (fun {j k} a ↦ qaB j k a) (fun {j k} a ↦ qaA j k a)
    hd hbeta hdelta hdj (fun {j k} a ↦ hqaB j k a) (fun {j k} a ↦ hqaA j k a)
  refine ⟨o.c, d, o.cB, o.cA, o.lambda, beta, delta, o.cj, dj, o.hc, hd, ?_, ?_, ?_⟩
  · intro j
    exact ⟨o.hcB j, o.hcA j, o.hcj j, hbeta j, hdelta j, hdj j,
      o.counit j, hc.counit j, hc.transpose j, hc.coefficient j⟩
  · intro j k a
    exact ⟨o.caB a, qaB j k a, o.hcaB a, hqaB j k a, hc.transitionB a⟩
  · intro j k a
    exact ⟨o.caA a, qaA j k a, o.hcaA a, hqaA j k a, hc.transitionA a⟩

end CategoryTheory.AlgebraDiagramAdjunctionPresentation
