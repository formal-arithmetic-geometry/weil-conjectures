/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.PointModelFreeModule
public import WeilConjectures.AlgebraicGeometry.PointModelPullbackFunctor
public import WeilConjectures.AlgebraicGeometry.PointModelRestrictionModule
import WeilConjectures.AlgebraicGeometry.DiscretePointPresentationTransport
import all WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent

/-! # Refinement of one discrete point presentation

## References

* Stacks Project, Tags 03CY, 00YV and 09AJ
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

private theorem local_cokernel_of_slice_matrix
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (k : Type (u + 1)) [CommRing k] (F : Sheaf J (ModuleCat.{u + 1} k))
    (U : C) (m n : ℕ)
    (a : (constantSheaf (J.over U) (ModuleCat.{u + 1} k)).obj
        (ModuleCat.of k (Fin m → k)) ⟶
      (constantSheaf (J.over U) (ModuleCat.{u + 1} k)).obj
        (ModuleCat.of k (Fin n → k)))
    (h : F.over U ≅ cokernel a) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (g : V ⟶ U), S g →
        ∃ q : ModuleCat.of k (Fin m → k) ⟶ ModuleCat.of k (Fin n → k),
          Nonempty (F.over V ≅
            (constantSheaf (J.over V) (ModuleCat.{u + 1} k)).obj (cokernel q)) := by
  classical
  obtain ⟨S, hS, hs⟩ := CategoryTheory.exists_sieve_overMap_maps J k U
    (fun _ : Unit ↦ ModuleCat.of k (Fin m → k))
    (fun _ : Unit ↦ ModuleCat.of k (Fin n → k)) (fun _ ↦ a)
  refine ⟨S, hS, ?_⟩
  intro V g hg
  by_cases hb : (⊥ : Sieve V) ∈ J V
  · refine ⟨0, ⟨?_⟩⟩
    exact (CategoryTheory.over_sheaf_isZero J k V hb (F.over V)).iso
      (CategoryTheory.over_sheaf_isZero J k V hb _)
  · obtain ⟨q, hq⟩ := hs g hg hb ()
    let P := J.overMapPullback (ModuleCat.{u + 1} k) g
    have : PreservesColimitsOfSize.{u + 1, u + 1} P :=
      ((Over.map g).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} k)
        (J.over V) (J.over U)).leftAdjoint_preservesColimits
    let im := CategoryTheory.constantOverMapIso J k g (ModuleCat.of k (Fin m → k))
    let iN := CategoryTheory.constantOverMapIso J k g (ModuleCat.of k (Fin n → k))
    refine ⟨q, ⟨(Sheaf.pushforwardOverMapIso F g).symm ≪≫ P.mapIso h ≪≫
      PreservesCokernel.iso P a ≪≫
      cokernel.mapIso _ ((constantSheaf (J.over V) (ModuleCat.{u + 1} k)).map q)
        im.symm iN.symm ?_ ≪≫
      (PreservesCokernel.iso (constantSheaf (J.over V) (ModuleCat.{u + 1} k)) q).symm⟩⟩
    change im.hom ≫ P.map a = _ ≫ iN.hom at hq
    change P.map a ≫ iN.inv = im.inv ≫ _
    apply (cancel_epi im.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc] using
      congrArg (fun b ↦ b ≫ iN.inv) hq

/-- A single finite presentation on the condensed point gives constant finite presentations
locally after section reconstruction and arbitrary coefficient relabelling. There is no
local-model hypothesis on N: the displayed isomorphism is one specified finite-matrix cokernel.
(Stacks, Tags 03CY and 00YV) -/
theorem discrete_point_presentation_refinement
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type u) [CommRing A] (k : Type (u + 1)) [CommRing k]
    (e : ULift.{u + 1} A ≃+* k)
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj (discreteObj A) X))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj A) X))
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y)
    (m n : ℕ)
    (d : pointModelFree (discreteObj A) m ⟶ pointModelFree (discreteObj A) n)
    (hN : Nonempty
        (pointModelRestriction (discreteObj A) f N (AsSmall.down.obj U).hom ≅
          (pointModelPullbackFunctor (discreteObj A) (AsSmall.down.obj U).left).obj (cokernel d))) :
    ∃ S : Sieve U, S ∈ Scheme.coefficientProEtaleModelTopology.{u, u} Y U ∧
      ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (g : V ⟶ U), S g →
        ∃ q : ModuleCat.of k (Fin m → k) ⟶ ModuleCat.of k (Fin n → k),
          Nonempty (((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
          ((coefficientModelFixedScalars _ k).obj
            ((smallModules X (condensedRingObj (discreteObj A) X) ⋙
              ConstantCompletion.res c.hom).obj N))).over V ≅
            (constantSheaf
              ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over V)
              (ModuleCat.{u + 1} k)).obj (cokernel q)) := by
  let F := ((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
    ((coefficientModelFixedScalars _ k).obj
      ((smallModules X (condensedRingObj (discreteObj A) X) ⋙
        ConstantCompletion.res c.hom).obj N)))
  obtain ⟨a, ⟨ha⟩⟩ := discrete_point_presentation_transport f A k e c N U m n d hN
  obtain ⟨S, hS, hSV⟩ := local_cokernel_of_slice_matrix
    (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k F U m n a ha
  refine ⟨S, hS, ?_⟩
  intro V g hg
  obtain ⟨q, hq⟩ := hSV V g hg
  exact ⟨q, hq⟩

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
