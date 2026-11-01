/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FourierSetting
public import WeilConjectures.AlgebraicGeometry.CondensedFourierKernel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.FourierTransform.Properties.BaseChange
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum

import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing

/-! # The specified Fourier base-change comparison

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/lem-fd-base-change.proof.md,
compact-support exchange, pullback of the integrand and kernel, and shift
(blueprint: def-fd-canonical-base-change-comparison).

## Main definitions

* `FourierBaseChangeDiagram`: finite-field descent and the Cartesian geometric diagram.
* `FourierBaseChangeDiagram.kernelComparison`: the normalized kernel identification.
* `FourierBaseChangeDiagram.boundedBaseChangeComparison`: the specified comparison morphism.
* `FourierBaseChangeDiagram.baseChangeIso`: its inverse and isomorphism structure.

## Main statements

* `FourierBaseChangeDiagram.comparison_bounded`: both endpoints are bounded constructible.
* `FourierBaseChangeDiagram.baseChangeComparison_isIso`: the comparison is invertible.
* `FourierBaseChangeDiagram.baseChangeComparison_naturality`: naturality in the input.

The geometric diagram is recorded after extension to the algebraic closure. It admits arbitrary
Cartesian presentations of the two base-changed bundles. No comparison is selected from the
existence theorem for Fourier base change: every factor below is a specified structural map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

namespace FourierBaseChangeDiagram

variable {F : WeilConjectures.FourierSetting.{u}} (d : FourierBaseChangeDiagram F)
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Evaluate a natural transformation between the concrete derived module categories.
This is exactly its usual component; the generic scheme parameters fix the category
presentation before a Fourier integrand is substituted.
Source: latest blueprint, lem-fd-base-change.proof.md, compact-support comparison
(blueprint: def-fd-canonical-base-change-comparison). -/
def condensedComponent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    {A B : (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) ⥤ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))}
    (α : A ⟶ B) (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) : A.obj M ⟶ B.obj M :=
  α.app M

private theorem condensedComponent_isIso_of_heq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    {A B A' B' : (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) ⥤ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))}
    (hA : A = A') (hB : B = B') (α : A ⟶ B) (α' : A' ⟶ B')
    (hα : HEq α α') (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (h : IsIso (α'.app M)) : IsIso (condensedComponent Λ α M) := by
  cases hA
  cases hB
  cases hα
  exact h

private theorem condensedComponent_naturality_inv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    {A B : (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) ⥤ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))}
    (α : A ⟶ B) {M N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hM : IsIso (condensedComponent Λ α M))
    (hN : IsIso (condensedComponent Λ α N)) (f : M ⟶ N) :
    B.map f ≫ inv (condensedComponent Λ α N) =
      inv (condensedComponent Λ α M) ≫ A.map f := by
  letI : IsIso (α.app M) := hM
  letI : IsIso (α.app N) := hN
  exact (NatTrans.naturality_inv α f).symm

set_option maxHeartbeats 1200000 in
-- Coefficient transport and derived tensor involve large categorical instance terms.
universe v w

/-- The proper pullback is independent of the presentation of the upper Cartesian square.
Cancel the invertible literal open factor and insert the invertible open factor for `sq`.
Source: the proper/open composite in det-prop-sf-cbc (blueprint:
def-fd-canonical-base-change-comparison). -/
private theorem isIso_exchange_of_literal
    (C : CompactSupportFormalism.{w, v, u}) [C.HasBaseChange]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (c : Compactification f) (M : C.obj X)
    (h : IsIso ((C.shriekBaseChange c (c.baseChange g) (pullback.fst c.g g)
      (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f g))
      (c.isPullback_g_ofIsPullback (IsPullback.of_hasPullback f g)).flip).natTrans.app M)) :
    IsIso ((C.shriekBaseChange c (c.ofIsPullback sq) (pullback.fst c.g g)
      (c.isPullback_i_ofIsPullback sq)
      (c.isPullback_g_ofIsPullback sq).flip).natTrans.app M) := by
  let sq₀ := IsPullback.of_hasPullback f g
  letI hOpenLiteral := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := C)
    (c.isPullback_i_ofIsPullback sq₀)
  letI hOpenActual := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := C)
    (c.isPullback_i_ofIsPullback sq)
  letI hOpenLiteralComponent : IsIso
      ((C.baseChange (pullback.fst f g) (c.baseChange g).i c.i
        (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq₀).w).natTrans.app M) := by
    change IsIso ((C.baseChange (pullback.fst f g) (c.ofIsPullback sq₀).i c.i
      (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq₀).w).natTrans.app M)
    infer_instance
  letI hOpenActualComponent := NatIso.isIso_app_of_isIso
    (C.baseChange g' (c.ofIsPullback sq).i c.i
      (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq).w).natTrans M
  dsimp only [CompactSupportFormalism.shriekBaseChange] at h ⊢
  rw [ExchangeFormalism.shriekBaseChange_app] at h ⊢
  simp only [Compactification.baseChange_g] at h
  letI hLiteralComponent := h
  letI hProperComponent : IsIso ((C.pfBaseChange (pullback.fst c.g g)
      (pullback.snd c.g g) c.g g pullback.condition).natTrans.app ((C.sh c.i).obj M)) :=
    IsIso.of_isIso_comp_right _ ((C.pf (pullback.snd c.g g)).map
      (inv ((C.baseChange (pullback.fst f g) (c.baseChange g).i c.i
        (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq₀).w).natTrans.app M)))
  change IsIso ((C.pfBaseChange (pullback.fst c.g g) (pullback.snd c.g g)
    c.g g pullback.condition).natTrans.app ((C.sh c.i).obj M) ≫
      (C.pf (pullback.snd c.g g)).map
        (inv ((C.baseChange g' (c.ofIsPullback sq).i c.i
          (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq).w).natTrans.app M)))
  infer_instance

/-- Instantiate the formal cancellation before substituting geometric product schemes. -/
private theorem condensed_isIso_exchange_of_literal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (c : Compactification f)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h : IsIso (((compactSupportCondensedFormalism Λ).shriekBaseChange c (c.baseChange g)
      (pullback.fst c.g g)
      (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f g))
      (c.isPullback_g_ofIsPullback (IsPullback.of_hasPullback f g)).flip).natTrans.app M)) :
    IsIso (((compactSupportCondensedFormalism Λ).shriekBaseChange c (c.ofIsPullback sq)
      (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq)
      (c.isPullback_g_ofIsPullback sq).flip).natTrans.app M) := by
  exact isIso_exchange_of_literal (compactSupportCondensedFormalism Λ) sq c M h

/-- Expose the category fields without expanding the proper/open comparison. -/
private def concreteFormalism
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : CompactSupportFormalism :=
  { compactSupportCondensedFormalism Λ with
    obj := fun X ↦ DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    category := fun _ ↦ inferInstance }

/-- The exposed presentation has exactly the same formalism data. -/
private theorem concreteFormalism_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    concreteFormalism Λ = compactSupportCondensedFormalism Λ := by
  unfold concreteFormalism compactSupportCondensedFormalism
  rfl

/-- Transport open base change along the equality of presentations. -/
private instance concreteFormalism_hasBaseChange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : (concreteFormalism Λ).HasBaseChange := by
  rw [concreteFormalism_eq]
  infer_instance

/-- A typed derived-category interface for the specified formal exchange. -/
private def condensedExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification Λ c ⋙
        (upperStar Λ g).leftDerivedFunctor ⟶
      (upperStar Λ g').leftDerivedFunctor ⋙
        rightDerivedLowerShriekOfCompactification Λ (c.ofIsPullback sq) :=
  ((compactSupportCondensedFormalism Λ).shriekBaseChange c (c.ofIsPullback sq)
    (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq)
    (c.isPullback_g_ofIsPullback sq).flip).natTrans

private def natTransSource {C D : Type*} [Category C] [Category D]
    {A B : C ⥤ D} (_α : A ⟶ B) : C ⥤ D := A

private def natTransTarget {C D : Type*} [Category C] [Category D]
    {A B : C ⥤ D} (_α : A ⟶ B) : C ⥤ D := B

set_option maxHeartbeats 1200000 in
-- The bounded integrand is specialized to geometric product schemes.
set_option maxHeartbeats 1200000 in
-- The kernel normalizes endpoint identities across several total-derived functor interfaces.
set_option maxHeartbeats 1200000 in
-- The endpoint identifications cross derived pullback, compact support, and shift interfaces.
/-- The map formula for tensoring on the right, without unfolding its category instance. -/
private theorem tensorRight_map_eq {C : Type*} [Category C] [MonoidalCategory C]
    (B : C) {X Y : C} (f : X ⟶ Y) : (tensorRight B).map f = f ▷ B := by
  rfl

set_option maxHeartbeats 1200000 in
-- Tensor and pullback naturality cross total-derived functor interfaces.
set_option maxHeartbeats 1200000 in
-- The composite natural transformation has several derived endpoint identifications.
end FourierBaseChangeDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
