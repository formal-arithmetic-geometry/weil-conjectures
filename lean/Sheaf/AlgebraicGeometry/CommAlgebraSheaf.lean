/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Sheaves of commutative algebras on a scheme

Source: Stacks Project, Properties, Tag 05JT; Modules, algebras on ringed spaces
(blueprint: def-weil-pbc-comm-algebra-sheaf).
-/

@[expose] public section

universe uA

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Sheaves of commutative `𝒪_X`-algebras are commutative ring sheaves equipped with a
morphism from the structure sheaf. Morphisms commute with that structure morphism.
Source: Stacks Project, Properties, Tag 05JT
(blueprint: def-weil-pbc-comm-algebra-sheaf). -/
abbrev CommAlgebraSheaf (X : Scheme.{uA}) := Under X.sheaf

/-- The underlying `𝒪_X`-module is the rank-one module over the algebra sheaf, restricted
along its structure morphism. Source: Stacks Project, Properties, Tag 05JT
(blueprint: def-weil-pbc-comm-algebra-sheaf). -/
noncomputable def CommAlgebraSheaf.toModule {X : Scheme.{uA}} (A : X.CommAlgebraSheaf) :
    SheafOfModules.{uA} X.ringCatSheaf :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat)).map A.hom)).obj
    (SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat)).obj A.right))

end AlgebraicGeometry.Scheme
