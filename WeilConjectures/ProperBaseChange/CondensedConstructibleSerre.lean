/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ProperBaseChange.CondensedFieldLfpLocalTriviality
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.ProperBaseChange.ProfiniteTestObjectFunctor
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.ProperBaseChange.CondensedFieldContinuousRealization
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.ProperBaseChange.GeometricFieldProfiniteDenseSubsite
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
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
import WeilConjectures.ProperBaseChange.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.ProperBaseChange.CondensedQbarFieldEvaluationLinearity
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.CategoryTheory.ModuleObjects.Free

/-!
# Serre closure for constructible condensed field module sheaves

Source: upstream `ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean`, Sorried input;
Bhatt--Scholze, Section 6.8, Lemma 6.8.7 and Corollary 6.8.9
(blueprint: lem-weil-pbc-condensed-constructible-serre).

The coefficients are pulled back from condensed abelian groups. Algebraic-closure sections
have image in a single finite intermediate field, as in `Profinite.padicAlgClRingObj`.
Constructibility is stratified local finite presentation, with no completeness condition.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory MonObj in
private lemma fp_of_iso {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] {R : C} [MonObj R]
    [PreservesFiniteColimits (tensorLeft R)] {M N : Mod C R}
    (h : Mod.IsFinitelyPresented R M) (e : M ≅ N) : Mod.IsFinitelyPresented R N := by
  obtain ⟨n, m, f, ⟨i⟩⟩ := h
  exact ⟨n, m, f, ⟨e.symm ≪≫ i⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma fp_map {X Y : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, f, ⟨i⟩⟩ := h
  let en (n : ℕ) : F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫ biproduct.mapIso (fun _ ↦ e)
  let f' : Mod.finiteFree S m ⟶ Mod.finiteFree S n :=
    (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma fp_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFinitelyPresented S M) :
    Mod.IsFinitelyPresented R ((Mod.comap φ).obj M) := by
  apply fp_map (Mod.comap φ) _ h
  simpa using Mod.regularIsoOfIsIso (inv φ)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) (e : M ≅ N) : Mod.IsFree R N := by
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨n, ⟨e.symm ≪≫ i⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_map {X Y : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) : Mod.IsFree S (F.obj M) := by
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨n, ⟨F.mapIso i ≪≫ F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ e)⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) :
    Mod.IsFree ((upperStar Ab.{u + 1} g).obj R)
      (((upperStar Ab.{u + 1} g).mapMod R).obj M) := by
  exact free_map ((upperStar Ab.{u + 1} g).mapMod R)
    (Mod.isoMk (Iso.refl _) (by simp [Mod.act])) h

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree S M) : Mod.IsFree R ((Mod.comap φ).obj M) := by
  apply free_map (Mod.comap φ) _ h
  simpa using Mod.regularIsoOfIsIso (inv φ)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_of_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree R ((Mod.comap φ).obj M)) : Mod.IsFree S M := by
  exact free_of_iso (free_comap (inv φ) h)
    ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_pullback_comp_iff {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    Mod.IsFree ((upperStar Ab.{u + 1} (f ≫ g)).obj R)
      (((upperStar Ab.{u + 1} (f ≫ g)).mapMod R).obj M) ↔
    Mod.IsFree ((upperStar Ab.{u + 1} f).obj ((upperStar Ab.{u + 1} g).obj R))
      (((upperStar Ab.{u + 1} f).mapMod _).obj
        (((upperStar Ab.{u + 1} g).mapMod R).obj M)) := by
  let F := upperStar Ab.{u + 1} g
  let G := upperStar Ab.{u + 1} f
  let e := upperStarComp Ab.{u + 1} f g
  let φ := Functor.compAlgHom F G e.inv R
  let i := (Functor.mapModCompIso F G e.inv R).app M
  exact ⟨fun h ↦ free_of_iso (free_comap φ h) i.symm,
    fun h ↦ free_of_comap φ (free_of_iso h i)⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma common_free_cover {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M))
    (hN : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj N)) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M) ∧
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj N) := by
  obtain ⟨U, hU⟩ := hM
  obtain ⟨V, hV⟩ := hN
  refine ⟨U.bind (fun i ↦ V.pullback₁ (U.f i)), fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  constructor
  · exact (free_pullback_comp_iff (pullback.fst (U.f i) (V.f j)) (U.f i) M).mpr
      (free_pullback (pullback.fst (U.f i) (V.f j)) (hU i))
  · change Mod.IsFree
      ((upperStar Ab.{u + 1} (pullback.fst (U.f i) (V.f j) ≫ U.f i)).obj R)
      (((upperStar Ab.{u + 1} (pullback.fst (U.f i) (V.f j) ≫ U.f i)).mapMod R).obj N)
    rw [pullback.condition]
    exact (free_pullback_comp_iff (pullback.snd (U.f i) (V.f j)) (V.f j) N).mpr
      (free_pullback (pullback.snd (U.f i) (V.f j)) (hV j))

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma lfp_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsLocallyFinitelyPresented S M) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj M) := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (U.f i)
  exact fp_of_iso (fp_comap (F.map φ) (hU i)) ((F.mapModComapIso φ).app M).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma locally_free_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj S)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod S).obj M)) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj ((Mod.comap φ).obj M)) := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (U.f i)
  exact free_of_iso (free_comap (F.map φ) (hU i)) ((F.mapModComapIso φ).app M).symm

end AlgebraicGeometry.ProEtale
