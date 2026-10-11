/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Enough injectives for constant-coefficient etale module sheaves

Source: Stacks Project, Injectives, Theorems 01DU and 079H; used in Etale Cohomology,
Lemma 0A4C, first paragraph of the proof
(blueprint: lem-weil-pbc-module-sheaves-enough-injectives).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Sheaves of modules over the constant ring sheaf on the small etale site have enough
injectives, as do abelian sheaves on that site. `EnoughInjectives` means that every object
has a monomorphism to an injective object in the same category. `ULift` places the ring
in the universe of the sheaf values without changing its ring structure.

Source: Stacks Project, Injectives, Theorems 01DU and 079H; Etale Cohomology, Lemma 0A4C
(blueprint: lem-weil-pbc-module-sheaves-enough-injectives).

Proof: By lem-weil-pbc-module-sheaves-grothendieck-abelian, the module sheaf category is
Grothendieck abelian: it is abelian, has small colimits, exact filtered colimits and a
generator obtained as the sum of the extension-by-zero free modules over representatives
of an essentially small dense subcategory of the small etale site. The same result for
integer coefficients gives the Grothendieck abelian property of abelian sheaves (Step 1).
Apply lem-sp-grothendieck-enough-injectives, Stacks 079H, to each category (Step 2).
Its functorial injective embedding sends each object F to an injective object I(F), with a
monomorphism F to I(F). Injectivity is inside the respective category, in the sense of
def-sp-injective-resolutions. These embeddings give both asserted EnoughInjectives
properties. -/
theorem etaleModule_enoughInjectives (T : Scheme.{u}) (R : Type u) [CommRing R] :
    EnoughInjectives (SheafOfModules.{u + 1}
      ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} R)))) ∧
      EnoughInjectives (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
  sorry

end AlgebraicGeometry.Scheme
