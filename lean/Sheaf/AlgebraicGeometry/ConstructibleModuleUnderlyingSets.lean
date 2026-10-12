/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Sheaf.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Constructibility after forgetting module structure

Source: Stacks Project, Tags 095E and 09Z6.
(blueprint: lem-weil-pbc-constructible-module-underlying-sets).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Finite module trivializations give a constructible underlying sheaf of sets.

Source: Stacks Project, Tag 095E(3), and the passage from (3) to (1) in Tag 09Z6.
(blueprint: lem-weil-pbc-constructible-module-underlying-sets).

Proof: Retain the finite locally closed partition witnessing module constructibility.
Its parts are constructible, so the same domains and immersions form a stratification
in the set-valued definition. Forgetting modules commutes with inverse image and with
restriction to each member of the trivializing etale cover. The underlying set of each
finite constant module is finite, and forgetting carries its constant sheaf to the
constant sheaf of this set. Hence the set pullback to every stratum is locally constant.
At any geometric point of that stratum, lift to a member of the cover. Its stalk is the
finite underlying set of that member's constant module, since stalks commute with
restriction and constants. Thus the pullback is finite locally constant on every
stratum, as required. The empty partition and the zero module cause no exception. -/
theorem isConstructibleEtaleSheafOfSets_of_module
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) := by sorry

end AlgebraicGeometry.Scheme
