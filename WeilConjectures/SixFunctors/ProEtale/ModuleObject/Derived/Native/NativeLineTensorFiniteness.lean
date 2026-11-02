/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible

/-! # Finiteness under tensor with a native locally free module

Source: current blueprint prop-weil-twist-preserves, cohomology and Tor arguments
(blueprint: lem-twist-native-line-tensor-finiteness).
The coefficient ring is pulled back from the condensed point. All derived tensors
are ordinary, uncompleted derived tensors; no Noetherian hypothesis is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

private def flatTensorComparison
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    let := hP.flat.tensorLeft.preservesFiniteLimits
    (DerivedCategory.singleFunctor _ 0).obj P ⊗ K ≅
      (tensorLeft P).mapDerivedCategory.obj K := by
  let := hP.flat.tensorLeft.preservesFiniteLimits
  let L := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  let S := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj P
  exact whiskerLeftIso _ e.symm ≪≫
    tensorIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app P) (Iso.refl _) ≪≫
    DerivedCategory.QObjTensorQObjIsoOfKFlatLeft S L
      ((CochainComplex.kFlat_single_obj_iff_flat P 0).2 hP.flat) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor _) P).app L) ≪≫
    ((tensorLeft P).mapDerivedCategoryFactors.app L).symm ≪≫
    (tensorLeft P).mapDerivedCategory.mapIso e

/-- Tensor with a locally free native coefficient module preserves constructible
cohomology and every cohomological and Tor interval, hence bounded constructibility
and finite Tor constructibility. Source: prop-weil-twist-preserves, steps 2--4
(blueprint: lem-twist-native-line-tensor-finiteness).
Proof: the locally free module is dualizable, hence flat. Its degree-zero single
complex is K-flat. The K-flat tensor comparison, the single-complex tensor formula,
and exact-functor descent identify derived tensor with termwise ordinary tensor.
The exact-functor homology comparison identifies its cohomology with the ordinary
tensor of cohomology. Ordinary tensor with a locally free module preserves the
same constructible strata and finite presentation models. Flatness gives Tor
amplitude [0,0]; the tensor amplitude estimate adds zero to both endpoints.
These arguments work for unbounded complexes and arbitrary schemes. -/
theorem nativeLineTensor_finiteness
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : IsLocallyFree (condensedRingObj Λ X) P) :
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
        (i : ℤ), Nonempty
      ((DerivedCategory.homologyFunctor _ i).obj
          (K ⊗ (DerivedCategory.singleFunctor _ 0).obj P) ≅
        P ⊗ (DerivedCategory.homologyFunctor _ i).obj K)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
        (a b : ℤ), DerivedCategory.homologyConcentratedIn a b K →
      DerivedCategory.homologyConcentratedIn a b
        (K ⊗ (DerivedCategory.singleFunctor _ 0).obj P)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
        (a b : ℤ), _root_.DerivedCategory.torAmplitudeIn _ a b K →
      _root_.DerivedCategory.torAmplitudeIn _ a b
        (K ⊗ (DerivedCategory.singleFunctor _ 0).obj P)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      boundedConstructible (condensedRingObj Λ X) K →
      boundedConstructible (condensedRingObj Λ X)
        (K ⊗ (DerivedCategory.singleFunctor _ 0).obj P)) ∧
    ∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      condensedConstructibleFiniteTor Λ X K →
      condensedConstructibleFiniteTor Λ X
        (K ⊗ (DerivedCategory.singleFunctor _ 0).obj P) := by
  let := hP.flat.tensorLeft.preservesFiniteLimits
  let := _root_.DerivedCategory.braidedCategory'
    (C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  have he (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
      K ⊗ (DerivedCategory.singleFunctor _ 0).obj P ≅
        (tensorLeft P).mapDerivedCategory.obj K :=
    β_ _ _ ≪≫ flatTensorComparison P hP K
  have hh (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) (i : ℤ) :
      (DerivedCategory.homologyFunctor _ i).obj
          (K ⊗ (DerivedCategory.singleFunctor _ 0).obj P) ≅
        P ⊗ (DerivedCategory.homologyFunctor _ i).obj K :=
    (DerivedCategory.homologyFunctor _ i).mapIso (he K) ≪≫
      (((tensorLeft P).mapDerivedCategoryHomologyFunctorIso i).app K).symm
  have ht := DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hP.flat
  have hi (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      (a b : ℤ) (hK : _root_.DerivedCategory.torAmplitudeIn _ a b K) :
      _root_.DerivedCategory.torAmplitudeIn _ a b
        (K ⊗ (DerivedCategory.singleFunctor _ 0).obj P) := by
    simpa only [add_zero] using DerivedCategory.torAmplitudeIn_tensor hK ht
  have hc (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      (hK : boundedConstructible (condensedRingObj Λ X) K) :
      boundedConstructible (condensedRingObj Λ X)
        (K ⊗ (DerivedCategory.singleFunctor _ 0).obj P) := by
    obtain ⟨⟨a, b, h⟩, hcons⟩ := (mem_boundedConstructible_iff _ K).mp hK
    apply (mem_boundedConstructible_iff _ _).mpr
    refine ⟨⟨a, b, fun i hi ↦ ?_⟩, fun i ↦ ?_⟩
    · exact ((tensorLeft P).map_isZero (h i hi)).of_iso (hh K i)
    · exact (hP.isConstructibleModuleObject_tensorObj (hcons i)).of_iso (hh K i).symm
  refine ⟨fun K i ↦ ⟨hh K i⟩, ?_, hi, hc, ?_⟩
  · intro K a b hK
    simpa only [add_zero] using
      DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_right hK ht
  · rintro K ⟨hK, a, b, htor⟩
    exact ⟨hc K hK, a, b, hi K a b htor⟩

end AlgebraicGeometry.ProEtale.CondensedRing
