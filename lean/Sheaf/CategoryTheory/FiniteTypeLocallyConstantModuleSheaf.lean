/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackage
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite type locally constant module sheaves on a small site

Source: Stacks Project, Modules on Sites, Tag 093U (3)
(blueprint: def-weil-pbc-finite-type-locally-constant-module-sheaf).
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

/-- A module sheaf is locally constant of finite type if every site object has a covering
sieve on whose members it is isomorphic to a constant finitely generated module sheaf.
Constants use the existing constant-module sheafification functor, restricted to the slice;
its canonical comparison with slice constants gives the usual definition. No points or
terminal object are required. Source: Stacks Project, Modules on Sites, Tag 093U (3)
(blueprint: def-weil-pbc-finite-type-locally-constant-module-sheaf). -/
def IsFiniteTypeLocallyConstant {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    (F : CategoryTheory.ringedSiteModules.{u}
      ((constantSheaf J RingCat.{u}).obj (RingCat.of B))) : Prop :=
  ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
    ∀ (V : C) (f : V ⟶ U), S f →
      ∃ M : ModuleCat.{u} B, Module.Finite B M ∧
        Nonempty (F.over V ≅ ((strictPerfectConstantSheaf J B).obj M).over V)

end SheafOfModules
