/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Localization.Predicate

/-! # The sequential derived-limit property for a derived strict tower

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
def-weil-pbc-derived-inverse-limit; Stacks Tags 08TC and 07KC
(blueprint: def-weil-pbc-derived-inverse-limit).

Evaluation retains the transitions of a strict tower. Localization transports this
entire inverse system. The derived-limit predicate makes no selection of a cone or functor.

## Main definitions

* `adicDerivedTowerEvaluation`: evaluation of the full derived inverse system.
* `IsAdicSequentialDerivedLimit`: existence of its distinguished Roos triangle.
-/

@[expose] public section

set_option autoImplicit false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Select the recorded locally-bijective description at the coefficient size t+1.
This is the existing small-site transport, with its size supplied explicitly; imported
max-universe instances otherwise leave an unresolved universe metavariable.
Source: Stacks Tag 03DA; blueprint def-weil-pbc-derived-inverse-limit
(blueprint: def-weil-pbc-derived-inverse-limit). -/
noncomputable instance (priority := 1100) adicModuleLocallyBijective (T : Scheme.{t}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : Scheme.AdicCoefficientDatum A)

/-- Termwise evaluation followed by localization, preserving the full transition diagram.
Source: blueprint def-weil-pbc-derived-inverse-limit; Stacks Tag 08TC
(blueprint: def-weil-pbc-derived-inverse-limit). -/
noncomputable def adicComplexTowerEvaluation :
    CochainComplex (Scheme.CompletedAdicTowers T d) ℤ ⥤ (ℕᵒᵖ ⥤
      DerivedCategory (Scheme.CompletedAdicModules T d)) :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight ℕᵒᵖ (CochainComplex (Scheme.CompletedAdicModules T d) ℤ)
      (DerivedCategory (Scheme.CompletedAdicModules T d))).obj DerivedCategory.Q

/-- Termwise evaluation of a tower quasi-isomorphism is pointwise invertible after
localization. Source: blueprint def-weil-pbc-derived-inverse-limit; Stacks Tag 05RU
(blueprint: def-weil-pbc-derived-inverse-limit).
Proof: homology of a tower is levelwise (lem-weil-tower-category-levelwise-abelian).
Evaluation therefore sends a quasi-isomorphism to one at each level. Localization
inverts each component, and a natural transformation with invertible components is
invertible. This includes every transition map of the inverse system. -/
theorem adicComplexTowerEvaluation_inverts :
    (HomologicalComplex.quasiIso (Scheme.CompletedAdicTowers T d) (ComplexShape.up ℤ)).IsInvertedBy
      (adicComplexTowerEvaluation T d) := by
  sorry

/-- Derived evaluation of the full strict tower, constructed by the localization lift.
Source: blueprint def-weil-pbc-derived-inverse-limit; Stacks Tag 08TC
(blueprint: def-weil-pbc-derived-inverse-limit). -/
noncomputable def adicDerivedTowerEvaluation :
    DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤ (ℕᵒᵖ ⥤
      DerivedCategory (Scheme.CompletedAdicModules T d)) :=
  Localization.lift (adicComplexTowerEvaluation T d) (adicComplexTowerEvaluation_inverts T d)
    DerivedCategory.Q

/-- The canonical factorization of derived tower evaluation on complexes.
Source: blueprint def-weil-pbc-derived-inverse-limit; Stacks Tag 05RU
(blueprint: def-weil-pbc-derived-inverse-limit). -/
noncomputable def adicDerivedTowerEvaluationFactors :
    DerivedCategory.Q ⋙ adicDerivedTowerEvaluation T d ≅ adicComplexTowerEvaluation T d :=
  Localization.fac (adicComplexTowerEvaluation T d) (adicComplexTowerEvaluation_inverts T d)
    DerivedCategory.Q

/-- An object is the sequential derived limit of M if its evaluated inverse system has a
product and this object admits the distinguished Roos triangle with middle map 1-s.
Only the property is defined: neither an object nor morphisms between limits are chosen.
Source: blueprint def-weil-pbc-derived-inverse-limit; Stacks Tag 08TC
(blueprint: def-weil-pbc-derived-inverse-limit). -/
def IsAdicSequentialDerivedLimit (M : DerivedCategory (Scheme.CompletedAdicTowers T d))
    (L : DerivedCategory (Scheme.CompletedAdicModules T d)) : Prop :=
  ∃ (_ : HasProduct (fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).obj (op n))),
    IsDerivedLimit
      (K := fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).obj (op n))
      (fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).map
        (homOfLE (Nat.le_succ n)).op) L

end AlgebraicGeometry.ProEtale
