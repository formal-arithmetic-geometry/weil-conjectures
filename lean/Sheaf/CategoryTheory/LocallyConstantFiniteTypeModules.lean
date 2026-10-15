/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.ConstantCoefficientScalarExtension
public import Mathlib.RingTheory.Finiteness.Defs

/-! # Local constant finite-module descriptions on a site

Source: Stacks Project, sites-cohomology.tex, Tags 094H and 094I
(blueprint: def-weil-pbc-locally-constant-finite-type-modules).
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

/-- Local trivializations by constant sheaves of finitely generated coefficient modules.
The module may vary with the member of the covering sieve; no points are used.
Source: Stacks Project, Tags 094H and 094I
(blueprint: def-weil-pbc-locally-constant-finite-type-modules). -/
def IsLocallyConstantFiniteTypeModules {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    (F : SheafOfModules.{u} (constantCoefficientRing J B)) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
    ∀ (U : C) (f : U ⟶ V), S f →
      ∃ M : ModuleCat.{u} B, Module.Finite B M ∧
        Nonempty (F.over U ≅ ((constantCoefficientModule J B).obj M).over U)

end SheafOfModules
