/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

/-!
# Blueprint statements

def-weil-pbc-constructible-complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- def-weil-pbc-constructible-complexes. -/
def DerivedCategory.isBoundedConstructible (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (T : Scheme.{u}) : ObjectProperty (DerivedCategoryModule Λ T) :=
  fun K ↦
    (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj K)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj K)

/-- def-weil-pbc-constructible-complexes. -/
def BoundedConstructibleDerivedCategory (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (T : Scheme.{u}) : Type _ :=
  (DerivedCategory.isBoundedConstructible Λ T).FullSubcategory

/-- Required definitions for . -/
noncomputable instance (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (T : Scheme.{u}) :
    Category (BoundedConstructibleDerivedCategory Λ T) :=
  inferInstanceAs (Category (DerivedCategory.isBoundedConstructible Λ T).FullSubcategory)

end AlgebraicGeometry.Etale
