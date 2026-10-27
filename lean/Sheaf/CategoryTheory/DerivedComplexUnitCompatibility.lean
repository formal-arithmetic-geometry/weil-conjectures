/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import all Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # Compatibility laws for the right-derived unit on complexes

The laws reuse the existing private comparison helpers.
Source: Stacks Tags 070I and 015F
(blueprint: lem-cbc-derived-complex-unit-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w₁ w₂ v₁ v₂ u₁ u₂
namespace CategoryTheory
open Abelian Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  [HasKInjectiveResolutions C]

/-- The right-derived unit transferred from homotopy complexes to complexes by the
canonical quotient comparison. This is an explicit composite, with no chosen data.
Source: Stacks Tag 015F (blueprint: lem-cbc-derived-complex-unit-compatibility). -/
@[no_expose] def derivedComplexUnit (F : C ⥤ D) [F.Additive] (J : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj J) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj J) :=
  (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj J) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app J)

/-- The explicit composite defining the transferred unit.
Source: Stacks Tag 015F (blueprint: lem-cbc-derived-complex-unit-compatibility). -/
theorem derivedComplexUnit_eq (F : C ⥤ D) [F.Additive] (J : CochainComplex C ℤ) :
    derivedComplexUnit F J =
      (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj J) ≫
        F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app J) := by
  unfold derivedComplexUnit
  rfl

/-- The transferred unit is inverse to its K-injective value isomorphism, is natural,
respects exact factorization, and restricts to the bounded-below derived unit.
Proof: reuse the existing four compatibility lemmas in the unbounded comparison
module. Their unit is the same explicit quotient-unit-quotient composite.
Source: Stacks Tags 070I and 015F
(blueprint: lem-cbc-derived-complex-unit-compatibility). -/
theorem derivedComplexUnitCompatibility :
    (∀ (F : C ⥤ D) [F.Additive] (J : CochainComplex C ℤ) [J.IsKInjective],
      derivedComplexUnit F J ≫ (F.rightDerivedFunctorObjQIso J).hom = 𝟙 _) ∧
    (∀ (F : C ⥤ D) [F.Additive] {J I : CochainComplex C ℤ} (ρ : J ⟶ I),
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map ρ) ≫
        derivedComplexUnit F I =
        derivedComplexUnit F J ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map ρ)) ∧
    (∀ (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      (J : CochainComplex C ℤ),
      F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient C (.up ℤ)).obj J) ≫
          F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app J) ≫
          F.mapDerivedCategoryFactors.hom.app J =
        (DerivedCategory.quotientCompQhIso D).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj J)) ∧
    (∀ [EnoughInjectives C] (F : C ⥤ D) [F.Additive] (K : HomotopyCategory.Plus C),
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
          F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.Plus.ι C).obj K)) := by
  exact ⟨AlgebraicGeometry.Etale.right_unit_Q_obj_iso,
    AlgebraicGeometry.Etale.right_unit_Q_naturality,
    AlgebraicGeometry.Etale.exact_factor_Q,
    fun [_] F [_] K ↦ AlgebraicGeometry.Etale.right_derived_plus_unit F K⟩

end CategoryTheory
