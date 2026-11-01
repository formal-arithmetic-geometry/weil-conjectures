/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange

/-! # Weil pairs on actual condensed modules

Source: latest blueprint, def-weil-weil-sheaf-complex, Weil-module and constructible
Weil-sheaf paragraphs (blueprint: def-weil-weil-sheaf-complex).

Weil modules are fixed pairs for exact pullback on actual condensed modules.
Weil complexes live in the ordinary derived category of those Weil modules.
Strict Weil complexes are pairs in the underlying bounded constructible derived category.
The canonical realization forgets a derived Weil module and retains its derived structure
isomorphism; it does not identify the two categories or assert faithfulness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- Actual Weil modules are the existing fixed-pair category on module pullback.
Source: latest blueprint, the displayed theta in the Weil-module paragraph
(blueprint: def-weil-weil-sheaf-complex). -/
abbrev condensedWeilModules
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y : Scheme.{u}} (g : Y ⟶ Y) :=
  CategoryTheory.Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ g)

section Derived

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {Y : Scheme.{u}} (g : Y ⟶ Y) [IsIso g]

end Derived

end WeilConjectures
