/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! # Intrinsic Koszul completion

Source: blueprint, proper base change, order 1257
(blueprint: def-weil-pbc-intrinsic-koszul-completion).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]

/-- Constant commutative ring sheafification unit, forgetting commutativity.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulConstantUnit :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{t + 1} Λ)) ⟶
      (adicModuleRing X Λ).obj :=
  Functor.whiskerRight
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} Λ))))
    (forget₂ CommRingCat RingCat)

set_option backward.isDefEq.respectTransparency false in
/-- Local bijectivity of the constant ring sheafification unit.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion).
Proof: forgetting commutativity preserves the underlying sections and local equalities;
the original sheafification unit is locally bijective. -/
theorem koszulConstantUnit_local :
    Presheaf.IsLocallyInjective (ProEt.topology X) (koszulConstantUnit X Λ) ∧
    Presheaf.IsLocallySurjective (ProEt.topology X) (koszulConstantUnit X Λ) := by
  constructor
  · rw [← Presheaf.isLocallyInjective_forget_iff]
    change Presheaf.IsLocallyInjective (ProEt.topology X)
      (Functor.whiskerRight
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} Λ))))
        (CategoryTheory.forget CommRingCat))
    infer_instance
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget]
    change Presheaf.IsLocallySurjective (ProEt.topology X)
      (Functor.whiskerRight
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} Λ))))
        (CategoryTheory.forget CommRingCat))
    infer_instance

/-- Constant module sheaves, obtained by actual module sheafification.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulConstantFunctor :
    ModuleCat.{t + 1} (ULift.{t + 1} Λ) ⥤
      SheafOfModules.{t + 1} (adicModuleRing X Λ) :=
  haveI := (koszulConstantUnit_local X Λ).1
  haveI := (koszulConstantUnit_local X Λ).2
  siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ) ⋙
    PresheafOfModules.sheafification (koszulConstantUnit X Λ)

/-- Constants preserve zero morphisms.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion).
Proof: the constant presheaf construction and module sheafification are additive. -/
theorem koszulConstantFunctor_preservesZero :
    (koszulConstantFunctor X Λ).PreservesZeroMorphisms := by
  constructor
  intro M N
  apply (SheafOfModules.toSheaf.{t + 1} (adicModuleRing X Λ)).map_injective
  change (presheafToSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map
    ((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ)).map
        (0 : M ⟶ N))) = 0
  have h : (PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ)).map
        (0 : M ⟶ N)) = 0 := by rfl
  rw [h, Functor.map_zero]

attribute [local instance] koszulConstantFunctor_preservesZero

end AlgebraicGeometry.Scheme
