/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.CondensedActionModule
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-! # Discrete lattice invariants and finite Koszul coordinates

Source: main-20261015, direct-image stability proof, paragraph (3), algebraic lattice input;
Stacks Tags 0623 and 062F (blueprint: lem-sfb-discrete-lattice-koszul-resolution).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Profinite.DiscreteLattice

/-- Internal modules in the recorded profinite-site convention.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
abbrev Modules (R : Profinite.CondensedRing.{u}) :=
  Profinite.CondensedAction.Modules R

/-- The multiplicative presentation of the additive lattice with its ordered basis.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
abbrev Group (r : ℕ) := Multiplicative (Fin r → ℤ)

/-- Discrete actions, equivalently commuting module automorphisms.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
abbrev Equivariant (R : Profinite.CondensedRing.{u}) (r : ℕ) := Action (Modules R) (Group r)

/-- Invariants are the actual limit of the one-object action diagram.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
def invariants (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ) :
    Equivariant R r ⥤ Modules R :=
  (Action.functorCategoryEquivalence (Modules R) (Group r)).functor ⋙ lim

/-- Invariants preserve addition.
Source: paragraph (3), DAG step 1 (blueprint: lem-sfb-discrete-lattice-koszul-resolution).
Proof: the limit inclusion is monic, and its composites with the maps induced by f+g
and by the sum of the induced maps both equal (f+g) on the underlying module. -/
theorem invariants_additive (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ) :
    (invariants R r).Additive := by
  constructor
  intro P Q f g
  change limMap ((Action.functorCategoryEquivalence (Modules R) (Group r)).functor.map
    (f + g)) = _
  rw [Functor.map_add]
  apply limit.hom_ext
  intro j
  simp only [invariants, Functor.comp_map, lim_map, limMap_π, Preadditive.add_comp,
    NatTrans.app_add, Preadditive.comp_add]

attribute [instance] invariants_additive

/-- Use the standard localization universe without restricting the coefficient universe.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
instance modulesDerived (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] :
    HasDerivedCategory.{u + 2} (Modules R) := HasDerivedCategory.standard _

end Profinite.DiscreteLattice
