/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace

import all WeilConjectures.ProperBaseChange.ProfiniteTestObjectFunctor
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Local triviality over continuous p-adic field coefficients

Source: Hemo--Richarz--Scholbach, Example 3.1, and the agent rank/descent argument
recorded in (blueprint: lem-weil-pbc-condensed-field-continuous-realization).
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K]
    [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    [(J.W (A := AddCommGrpCat.{w})).IsMonoidal]
    [(K.W (A := AddCommGrpCat.{w})).IsMonoidal]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

end CategoryTheory


namespace AlgebraicGeometry.ProEtale

private noncomputable def absoluteProjection (S : Profinite.{u}) : C(profiniteToScheme.obj S, S) :=
  ContinuousMap.fst.comp
    ⟨(LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm,
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous⟩
private lemma absoluteProjection_natural {S T : Profinite.{u}} (f : S ⟶ T) :
    (absoluteProjection T).comp (profiniteToScheme.map f).base.hom =
      f.hom.hom.comp (absoluteProjection S) := by
  ext p
  obtain ⟨⟨s, q⟩, rfl⟩ :=
    (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).surjective p
  simp only [ContinuousMap.comp_apply, absoluteProjection, ContinuousMap.fst_apply,
    ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)).symm
      (PrimeSpectrum.comap _ (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)
        (s, q)))).1 = f s
  have h : PrimeSpectrum.comap (LocallyConstant.comapRingHom f.hom.hom)
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ) (s, q)) =
      LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ) (f s, q) := by
    ext g
    rfl
  erw [h]
  exact congrArg Prod.fst
    ((LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)).symm_apply_apply (f s, q))
private lemma profiniteTestProjection_natural (X : Scheme.{u}) {S T : Profinite.{u}} (f : S ⟶ T) :
    (profiniteTestProjection X T).comp ((profiniteToProEtOf X).map f).left.base.hom =
      f.hom.hom.comp (profiniteTestProjection X S) := by
  change ((absoluteProjection T).comp
      (pullback.fst (toSpecZ (profiniteToScheme.obj T)) (toSpecZ X)).base.hom).comp
      ((profiniteToProEtOf X).map f).left.base.hom = _
  rw [ContinuousMap.comp_assoc]
  have h : ((profiniteToProEtOf X).map f).left ≫
      pullback.fst (toSpecZ (profiniteToScheme.obj T)) (toSpecZ X) =
      pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X) ≫ profiniteToScheme.map f := by
    dsimp [profiniteToProEtOf, MorphismProperty.Over.pullback]
    exact pullback.lift_fst _ _ _
  have h' := congrArg (fun g ↦ g.base.hom) h
  change _ = f.hom.hom.comp ((absoluteProjection S).comp
    (pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X)).base.hom)
  change (absoluteProjection T).comp
      ((pullback.fst (toSpecZ (profiniteToScheme.obj T)) (toSpecZ X)).base.hom.comp
        ((profiniteToProEtOf X).map f).left.base.hom) = _
  change (pullback.fst (toSpecZ (profiniteToScheme.obj T)) (toSpecZ X)).base.hom.comp
      ((profiniteToProEtOf X).map f).left.base.hom =
    (profiniteToScheme.map f).base.hom.comp
      (pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X)).base.hom at h'
  erw [h']
  exact congrArg (fun g : C(profiniteToScheme.obj S, T) ↦
    g.comp (pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X)).base.hom)
      (absoluteProjection_natural f)

private noncomputable def comparisonAdjoint (X : Scheme.{u}) (E : Type u)
    [NormedField E] : Profinite.continuousCoefficientRingObj E ⟶
      (pointLowerStar.obj ((lowerStar AddCommGrpCat.{u + 1} (toSpecZ X)).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
            (continuousCoefficientRingSheaf X E)))) :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
        { toFun := fun f ↦ ULift.up (f.down.comp (profiniteTestProjection X S.unop))
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro S T f
       apply ConcreteCategory.hom_ext
       intro g
       apply ULift.ext
       change (g.down.comp f.unop.hom.hom).comp (profiniteTestProjection X T.unop) =
         (g.down.comp (profiniteTestProjection X S.unop)).comp
           ((profiniteToProEtOf X).map f.unop).left.base.hom
       simp only [ContinuousMap.comp_assoc]
       erw [profiniteTestProjection_natural] }⟩

private noncomputable def comparison (X : Scheme.{u}) (E : Type u) [NormedField E] :
    condensedRingObj (Profinite.continuousCoefficientRingObj E) X ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousCoefficientRingSheaf X E)) :=
  ((pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _).symm
      (comparisonAdjoint X E)

end AlgebraicGeometry.ProEtale
