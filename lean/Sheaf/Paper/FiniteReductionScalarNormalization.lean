/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Paper.IntegralCompletedTowerPullbackUniverses
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Sheaf.Paper.CoefficientRingedTensorHomModel
import all Sheaf.Paper.QuotientTensorScalarTowerComparison
import all Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.SecSmoothPurity.ModuleTensorGenerators

/-! # Scalar normalization of the strict finite reduction tower

Source: Stacks, Tags 03EK, 06YT and 06YU.
(blueprint: lem-a1-finite-reduction-scalar-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.tensorScalarLevelIso
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.unrestrictedIntegralReductionExistence
  WeilConjectures.IntegralOnSlice.reductionWitness
attribute [local implicit_reducible] SheafOfModules.KFlatTotalTensorModel.monoidal
  SheafOfModules.KFlatTotalTensorModel.tensor
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose
  WeilConjectures.IntegralOnSlice.Site WeilConjectures.IntegralOnSlice.siteCategory
  WeilConjectures.IntegralOnSlice.topology
  WeilConjectures.IntegralOnSlice.restrict WeilConjectures.IntegralOnSlice.ring
  WeilConjectures.IntegralOnSlice.finite WeilConjectures.IntegralOnSlice.projection
  WeilConjectures.PrincipalKoszulStrictReplacement.residue
  SheafOfModules.restrictScalars SheafOfModules.unit SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingProjectionUnrestricted
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
attribute [local instance] WeilConjectures.tensorMonoidal WeilConjectures.tensorZero
  WeilConjectures.tensorPreadditive WeilConjectures.tensorObjZero WeilConjectures.tensorHasTotal
attribute [local implicit_reducible] WeilConjectures.tensorMonoidal
  WeilConjectures.PrincipalKoszulStrictReplacement.tensorWith
  WeilConjectures.PrincipalKoszulStrictReplacement.targetTower
  WeilConjectures.PrincipalKoszulStrictReplacement.targetTowerMap
  CategoryTheory.Functor.map₂HomologicalComplex CategoryTheory.Functor.ofOpSequence
  CategoryTheory.Functor.ofSequence CategoryTheory.Functor.mapHomologicalComplex
  CochainComplex.singleFunctors
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.PrincipalKoszulStrictReplacement
  (sourceTower targetTower sourceTowerMap targetTowerMap comparison residue)
namespace WeilConjectures.FiniteReductionTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : Scheme.{t})

private theorem sliceTransition_eq (n : ℕ) :
    IntegralOnSlice.transition l E Y none n = unrestrictedIntegralTransition l E Y n := by
  apply (unrestrictedIntegralTransition_existsUnique l E Y n).unique
  · exact (IntegralOnSlice.transition_existsUnique l E Y none n).exists.choose_spec
  · exact (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec

private theorem reduction_step (P : CochainComplex (Modules l E Y) ℤ) (n : ℕ) :
    (((reductionComplex l E Y).obj P).asFunctor).map (homOfLE n.le_succ).op =
      (unrestrictedIntegralTransition l E Y n).app P := by
  apply HomologicalComplex.hom_ext
  intro i
  change (((Functor.ofOpSequence (unrestrictedIntegralTransition l E Y)).map
    (homOfLE n.le_succ).op).app P).f i = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]

private def scalarTowerIso (P : CochainComplex (Modules l E Y) ℤ) :
    targetTower l E Y P ≅ ((reductionComplex l E Y).obj P).asFunctor := by
  let a : targetTower l E Y P ⟶ ((reductionComplex l E Y).obj P).asFunctor :=
    NatTrans.ofOpSequence (fun n ↦ (tensorScalarLevelIso l E Y n P).hom) (by
      intro n
      rw [reduction_step]
      apply HomologicalComplex.hom_ext
      intro i
      have h := tensorScalarLevelIso_transition l E Y n P
      have ht := congrArg
        (fun τ ↦ (tensorScalarLevelIso l E Y (n + 1) P).hom ≫ τ.app P)
        (sliceTransition_eq l E Y n)
      with_unfolding_all exact congrArg (fun a ↦ a.f i) (h.trans ht))
  exact NatIso.ofComponents (fun n ↦ tensorScalarLevelIso l E Y n.unop P)
    (fun f ↦ a.naturality f)

private theorem scalarTowerIso_hom_app (P : CochainComplex (Modules l E Y) ℤ)
    (n : ℕᵒᵖ) :
    (scalarTowerIso l E Y P).hom.app n = (tensorScalarLevelIso l E Y n.unop P).hom := rfl

attribute [local irreducible] scalarTowerIso

/-- Total tensor with the restricted quotient is canonically scalar extension,
compatibly with every quotient transition and every map of representatives.
Source: Stacks, sites-cohomology.tex, Tags 06YT and 06YU; Modules on Sites 03EK.
(blueprint: lem-a1-finite-reduction-scalar-normalization).

Proof: the total tensor with S_n[0] has only the q=0 summand in each degree.
Its canonical coproduct identification is P^i tensor Res(S_n). Apply the symmetric
balanced scalar-extension isomorphism sending p tensor s to s tensor p. The inverse
sends the sheafified generator s tensor p back to p tensor s. Balancing and
sheafification make the two composites identities. The differential is d_P tensor
1, so the degreewise maps form a chain isomorphism. On generators both transition
squares send p tensor s to q(s) tensor p. Thus the isomorphisms are of strict
towers. Naturality follows on generators since both composites send p tensor s
to s tensor f(p). No flatness is needed for this ordinary chain identification;
the stated good-complex hypotheses merely restrict its domain. -/
theorem finite_reduction_scalar_normalization :
    ∃ e : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      (targetTower l E Y P ≅ ((reductionComplex l E Y).obj P).asFunctor),
      (∀ (P : CochainComplex (Modules l E Y) ℤ)
      (hP : integralOperationsGoodComplex l E Y P)
      (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ) (x : (P.X i).val.obj U)
      (s : (integralCoefficientSheaf l E Y n).obj.obj U),
    (((e P hP).hom.app (op n)).f i).val.app U
      (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology Y)
        (completedIntegralCommRingSheafUnrestricted l E Y) P
        ((CochainComplex.singleFunctor (Modules l E Y) 0).obj (residue l E Y n))
        i 0 i (add_zero i) U x
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (residue l E Y n)).inv.val.app U s)) =
      unrestrictedIntegralTensorSection l E Y n (P.X i) U s x) ∧
      ∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P')
          (hP : integralOperationsGoodComplex l E Y P)
          (hP' : integralOperationsGoodComplex l E Y P'),
        targetTowerMap l E Y f ≫ (e P' hP').hom =
          (e P hP).hom ≫
            (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
              ((reductionComplex l E Y).map f)) := by
  let e := fun P : CochainComplex (Modules l E Y) ℤ ↦ scalarTowerIso l E Y P
  refine ⟨fun P _ ↦ e P, ?_, ?_⟩
  · intro P hP n i U x s
    dsimp only [e]
    rw [scalarTowerIso_hom_app l E Y P (op n)]
    have hi := tensorScalarLevelIso_inv_generator l E Y n P i U s x
    have hgen :
        ((CochainComplex.mapBifunctorSingle₂Iso
          (concreteTensor l E Y) (residue l E Y n) P).inv.f i).val.app U
          (CategoryTheory.CochainPullback.moduleTmul
            (R := completedIntegralCommRingSheafUnrestricted l E Y)
            (P.X i) (residue l E Y n) U x s) =
        coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology Y)
          (completedIntegralCommRingSheafUnrestricted l E Y) P
          ((CochainComplex.singleFunctor (Modules l E Y) 0).obj (residue l E Y n))
          i 0 i (add_zero i) U x
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (residue l E Y n)).inv.val.app U s) := by
      rw [single_tensor_inv l E Y (residue l E Y n) P i]
      rw [← MonoidalCategory.id_tensorHom]
      have hm := CategoryTheory.CochainPullback.moduleTmul_map
        (R := completedIntegralCommRingSheafUnrestricted l E Y)
        (𝟙 (P.X i))
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (residue l E Y n)).inv U x s
      with_unfolding_all
        exact congrArg (fun z ↦
          (HomologicalComplex.ιMapBifunctor P
            ((CochainComplex.singleFunctor (Modules l E Y) 0).obj (residue l E Y n))
            (concreteTensor l E Y) (.up ℤ) i 0 i (add_zero i)).val.app U z) hm
    have hi' := hi.trans hgen
    have hcancel :
        ((tensorScalarLevelIso l E Y n P).hom.f i).val.app U
            (((tensorScalarLevelIso l E Y n P).inv.f i).val.app U
              (IntegralOnSlice.generator l E Y none n (P.X i) U s x)) =
          IntegralOnSlice.generator l E Y none n (P.X i) U s x := by
      with_unfolding_all
        exact congrArg (fun f ↦ (f.f i).val.app U
          (IntegralOnSlice.generator l E Y none n (P.X i) U s x))
          (tensorScalarLevelIso l E Y n P).inv_hom_id
    exact (congrArg (((tensorScalarLevelIso l E Y n P).hom.f i).val.app U) hi').symm.trans
      hcancel
  · intro P P' f hP hP'
    apply NatTrans.ext
    funext n
    simp only [NatTrans.comp_app, e, scalarTowerIso_hom_app]
    apply HomologicalComplex.hom_ext
    intro i
    with_unfolding_all
      exact congrArg (fun a ↦ a.f i) (tensorScalarLevelIso_natural l E Y n.unop f)

end WeilConjectures.FiniteReductionTower
