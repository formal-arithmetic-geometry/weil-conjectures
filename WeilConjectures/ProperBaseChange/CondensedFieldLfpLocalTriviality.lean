/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.Topology.NoetherianSpace


import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.ProperBaseChange.CondensedFieldEvaluationFunctors
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Local triviality over continuous p-adic field coefficients

Source: Hemo--Richarz--Scholbach, Example 3.1, and the agent rank/descent argument
recorded in (blueprint: lem-weil-pbc-condensed-lfp-local-triviality).
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma fp_map {X Y : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (T : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) [MonObj R] [MonObj T]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) T)
    [F.Additive] [Limits.PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular T)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented T (F.obj M) := by
  open Limits in
  rcases h with ⟨n, m, f, ⟨i⟩⟩
  let en (n : ℕ) : F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree T n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
      Limits.biproduct.mapIso (fun _ ↦ e)
  let f' : Mod.finiteFree T m ⟶ Mod.finiteFree T n :=
    (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ Limits.PreservesCokernel.iso F f ≪≫
    Limits.cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

private lemma fp_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) T}
    (h : Mod.IsFinitelyPresented T M) :
    Mod.IsFinitelyPresented R ((Mod.comap φ).obj M) := by
  let eqv : Mod _ T ≌ Mod _ R :=
    CategoryTheory.Equivalence.mk (Mod.comap φ) (Mod.comap (inv φ))
      ((Mod.comapId T).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapComp (inv φ) φ)
      ((Mod.comapComp φ (inv φ)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId R)
  have : (Mod.comap φ).IsEquivalence := eqv.isEquivalence_functor
  exact fp_map T R (Mod.comap φ) (by
    simpa using (Mod.regularIsoOfIsIso (inv φ))) h

private lemma lfp_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) T}
    (h : IsLocallyFinitelyPresented T M) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj M) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  let F := upperStar AddCommGrpCat.{u + 1} (C.f i)
  obtain ⟨n, m, f, ⟨e⟩⟩ := fp_comap (F.map φ) (hC i)
  exact ⟨n, m, f, ⟨(F.mapModComapIso φ).app M ≪≫ e⟩⟩

private lemma free_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) T}
    (h : Mod.IsFree T M) : Mod.IsFree R ((Mod.comap φ).obj M) := by
  let eqv : Mod _ T ≌ Mod _ R :=
    CategoryTheory.Equivalence.mk (Mod.comap φ) (Mod.comap (inv φ))
      ((Mod.comapId T).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapComp (inv φ) φ)
      ((Mod.comapComp φ (inv φ)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId R)
  have : (Mod.comap φ).IsEquivalence := eqv.isEquivalence_functor
  obtain ⟨n, ⟨e⟩⟩ := h
  refine ⟨n, ⟨(Mod.comap φ).mapIso e ≪≫ ?_⟩⟩
  exact (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular T) ≪≫
    Limits.biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))

private lemma free_of_iso {V : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) R}
    (h : Mod.IsFree R M) (e : M ≅ N) : Mod.IsFree R N := by
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨n, ⟨e.symm ≪≫ i⟩⟩

private lemma free_of_comap {V : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj T] (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) T}
    (h : Mod.IsFree R ((Mod.comap φ).obj M)) : Mod.IsFree T M := by
  let e : (Mod.comap (inv φ)).obj ((Mod.comap φ).obj M) ≅ M :=
    ((Mod.comapComp (inv φ) φ).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId T).app M
  exact free_of_iso (free_comap (inv φ) h) e

private lemma free_pullback_comp_iff {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}} [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R) :
    Mod.IsFree ((upperStar AddCommGrpCat.{u + 1} (f ≫ g)).obj R)
      (((upperStar AddCommGrpCat.{u + 1} (f ≫ g)).mapMod R).obj M) ↔
    Mod.IsFree ((upperStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} g).obj R))
      (((upperStar AddCommGrpCat.{u + 1} f).mapMod _).obj
        (((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj M)) := by
  let F := upperStar AddCommGrpCat.{u + 1} g
  let G := upperStar AddCommGrpCat.{u + 1} f
  let e := upperStarComp AddCommGrpCat.{u + 1} f g
  let φ := Functor.compAlgHom F G e.inv R
  let i := (Functor.mapModCompIso F G e.inv R).app M
  exact ⟨fun h ↦ free_of_iso (free_comap φ h) i.symm,
    fun h ↦ free_of_comap φ (free_of_iso h i)⟩

end AlgebraicGeometry.ProEtale
