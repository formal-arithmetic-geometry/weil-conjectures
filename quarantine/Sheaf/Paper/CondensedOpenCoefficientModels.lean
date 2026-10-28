/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.Paper.CondensedOpenCounitUnits

/-! # Coherent coefficient models and their scalar units

Source: purity transport, Steps 2--3, and the specified open-counit proof, Steps 1--3, 5--6.
(blueprint: lem-pur-condensed-open-coefficient-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open CondensedERealization
namespace WeilConjectures.CondensedOpenCounitRealization

variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- Choose one coefficient family with the canonical reduction calculus and the
specified proper/open factorization, together with its normalized scalar units.
This asserts no compatibility between condensed open counits.

Source: current blueprint sec-smooth-purity, sk-thm-purity-transport, Steps 2--3;
open-counit normalization proof Steps 1--3, 5--6
(blueprint: lem-pur-condensed-open-coefficient-models).

Proof: construct the compact-support coefficient family using the fixed calculus,
its actual reduction/limit adjunction, and the ordinary sectionwise limit models.
Localizing their quotient/pullback squares gives the realization model; the identity
on component sections gives its canonical bridge. Define the parent's realization
map by the proper counit mate followed by the inverse open-unit adjunct, conjugated
by the reconstruction and lattice comparisons. This is the normalized construction
of compact-support realization, and hence gives FactorNormalized over the given k;
no finite-field datum is used. The arbitrary-field factorization theorem supplies
this family; its q inverse and parentCoordinates/integralInverse formulas agree
by reconstruction-unit naturality and the triangle identities. Mating the
reduction/pullback square gives the
strict-system counit identity. Apply total limit and unit naturality, cancel the
reconstruction unit on a complete input, and obtain the second system identity.
For each T take scalar coefficient inclusion on sections. Its derived adjunct is
coefficient multiplication, an isomorphism on the regular module: on flat
representatives its inverse sends b to b tensor 1 tensor 1. The scalar-extension
adjunctions and exact restriction comparison give ScalarUnit.normalized. At d=0
these are the Tate multiplication maps. Restriction precomposes every coefficient
section, so multiplication commutes with restriction. The target coefficient unit
map is precisely leftDerivedUpperStarUnitIso, giving UnitNormalized. All maps are
constructed before finite evaluation; zero objects, empty schemes, and the identity
open require no separate choices. -/
theorem condensed_open_coefficient_models :
    ∃ (C : Models l k) (units : ∀ T : Base k, ScalarUnit l k C.coefficient T),
      FactorNormalized l k C ∧ SystemCounitNormalized l k C ∧ UnitNormalized l k C units := by
  sorry

end WeilConjectures.CondensedOpenCounitRealization
