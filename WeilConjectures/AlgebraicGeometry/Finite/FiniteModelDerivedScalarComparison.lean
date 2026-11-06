/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Derived scalar extension of the constant realization of an algebraic complex

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E, and 0D6D;
sites-modules.tex, Tag 093J.
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

attribute [local instance] ULift.algebra'

private abbrev coefficientLift (B : Type t) [CommRing B] :
    ModuleCat.{t} B ⥤ ModuleCat.{t + 1} (ULift.{t + 1} B) :=
  ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom

private def liftedTensorIso {A B : Type t} [CommRing A] [CommRing B]
    (q : A →+* B) (M : ModuleCat.{t} A) :
    (coefficientLift B).obj ((ModuleCat.extendScalars q).obj M) ≅
      (ModuleCat.extendScalars (RingHom.ulift.{t + 1, t + 1} q)).obj
        ((coefficientLift A).obj M) := by
  letI := q.toAlgebra
  exact (show ULift.{t + 1} (B ⊗[A] M) ≃ₗ[ULift.{t + 1} B]
      (ULift.{t + 1} B ⊗[ULift.{t + 1} A] ULift.{t + 1} M) from
    { (TensorProduct.AlgebraTensorModule.uliftEquiv A B B M).toAddEquiv with
      map_smul' := fun b x ↦
        (TensorProduct.AlgebraTensorModule.uliftEquiv A B B M).map_smul b.down x
    }).toModuleIso

private def liftedTensorComparison {A B : Type t} [CommRing A] [CommRing B]
    (q : A →+* B) :
    ModuleCat.extendScalars q ⋙ coefficientLift B ≅
      coefficientLift A ⋙ ModuleCat.extendScalars (RingHom.ulift.{t + 1, t + 1} q) := by
  letI := q.toAlgebra
  refine NatIso.ofComponents (liftedTensorIso q) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨x⟩
  induction x using TensorProduct.inductionOn with
  | tmul b m => rfl
  | add x y hx hy =>
    have h : (ULift.up (x + y) : ULift.{t + 1} _) = ULift.up x + ULift.up y := rfl
    simpa only [h, map_add] using congrArg₂ (· + ·) hx hy

private def scalarTransportIso {B C D : Type t} [CommRing B] [CommRing C] [CommRing D]
    (q : B →+* C) (ρ : C ≃+* D) :
    ModuleCat.extendScalars (ρ.toRingHom.comp q) ≅
      ModuleCat.extendScalars q ⋙ ModuleCat.restrictScalars.{t} ρ.symm.toRingHom := by
  let adj := (ModuleCat.extendRestrictScalarsAdj q).comp
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t} ρ.symm).toAdjunction
  exact ((adj.ofNatIsoRight (ModuleCat.restrictScalarsComp q ρ.toRingHom).symm).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj (ρ.toRingHom.comp q))).symm

end AlgebraicGeometry.Scheme
