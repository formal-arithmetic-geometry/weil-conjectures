/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Stalks commute with direct sums of sheaves of modules

Source: Stacks Project, Sheaves on Spaces, Section 6.29, Tag 009E, items (3) and (5)
(blueprint: lem-pc-stalk-direct-sums).
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite DirectSum
open TopCat.Presheaf

namespace SheafOfModules

open Classical in
/-- Stacks Project, Tag 009E, item (5) (blueprint: lem-pc-stalk-direct-sums).
The stalk of the sheaf coproduct is linearly isomorphic to the direct sum of the stalks.
The equation on germs specifies the canonical comparison in the stated direction.
Sectionwise commutativity makes the structure sheaf a sheaf of commutative rings,
as required by the ringed-space convention of `def-weil-locally-ringed-space-morphism`.

Proof: form the presheaf direct sum sectionwise, using
`lem-weil-pbc-presheaf-modules-colimits-sectionwise`. Its sheafification is the sheaf
coproduct by `lem-weil-pbc-module-sheaves-colimits-forgetful` (2) and
`def-weil-presheaf-modules-sheafification`. The sheafification unit induces an isomorphism
on stalks by `lem-weil-pbc-stalk-sheafification-space`; its linearity follows from
`def-weil-pbc-module-stalk`, representing a scalar and a section on a common neighbourhood.
The stalk of the presheaf direct sum maps to the direct sum of stalks componentwise.
For surjectivity, represent the finitely many nonzero germs on a common neighbourhood,
using the finite intersection of their neighbourhoods. For injectivity, a finitely
supported section whose component germs vanish restricts to zero on a finite intersection
of neighbourhoods where those components vanish. This map is linear by the germ formula
for scalar multiplication. Compose it with the inverse of the sheafification stalk map.
On the germ of a section in the i-th summand the composite is the i-th direct-sum injection,
which identifies the canonical map. These formulas also commute with morphisms of families.
-/
theorem exists_stalk_directSum_linearEquiv
    {X : TopCat.{u}} (R : X.Sheaf RingCat.{u}) (I : Type u)
    (_hcomm : ∀ (U : Opens X) (r s : R.obj.obj (op U)), r * s = s * r)
    (F : I → SheafOfModules.{u} R) (x : X) :
    ∃ e : (stalk (C := AddCommGrpCat.{u}) (X := X) (∐ F).val.presheaf x)
        ≃ₗ[stalk (C := RingCat.{u}) (X := X) R.obj x]
        (⨁ i : I, (stalk (C := AddCommGrpCat.{u}) (X := X) (F i).val.presheaf x)),
      ∀ (i : I) (U : Opens X) (hx : x ∈ U) (s : (F i).val.obj (op U)),
        e (germ (∐ F).val.presheaf U x hx ((Sigma.ι F i).val.app (op U) s)) =
          DirectSum.lof (stalk (C := RingCat.{u}) (X := X) R.obj x) I
            (fun j : I => ↑(stalk (C := AddCommGrpCat.{u}) (X := X) (F j).val.presheaf x)) i
            (germ (F i).val.presheaf U x hx s) := by
  sorry

end SheafOfModules
