/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated

/-! # Triangulated closure for the ell-adic finiteness coefficients

Stated per coefficient ring (`𝒪̲_E`, `E̲`, `ℚ̲̄_ℓ`, unit ball `O̲`). The field cases use local
finite freeness. The integral cases use the integral Serre
criterion. These are exactly the heart-closure inputs in the last step of blueprint
`lem-sfb-dc-tensor-preserves`.
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

namespace CondensedRing

variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The bounded constructible module-object category over `ℚ̲̄_ℓ` is triangulated.
(blueprint: lem-sfb-dc-ell-adic-triangulated) -/
theorem isTriangulated_boundedConstructible_ellAdic_padicAlgCl :
    (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).IsTriangulated :=
  isTriangulated_boundedConstructible_padicAlgClRingObj X ℓ

end CondensedRing
end AlgebraicGeometry.ProEtale
