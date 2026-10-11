/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.AlgebraicGeometry.PerfectComplex

/-! # Direct summands of perfect complexes

Source: literature/stacks-project/cohomology.tex, Tag 08CS (lemma-summands-perfect)
(blueprint: lem-pc-perfect-summand).
-/

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A direct summand of a perfect complex is perfect, and the complementary summand
is perfect as well. First, `lem-pc-perfect-pseudo-coherent-locally-finite-tor` gives
pseudo-coherence and Tor amplitude in an interval on a neighbourhood of each point.
Second, `lem-pc-pseudo-coherent-summand` gives pseudo-coherence of both summands.
Third, tensoring the decomposition with any module and taking cohomology shows that
vanishing outside that interval passes to both summands (Tag 08CK).
Finally, `lem-pc-pseudo-coherent-finite-tor-perfect` gives local perfectness, and
`def-pc-perfect-complex` gives perfectness on X for each summand.
Source: literature/stacks-project/cohomology.tex, Tag 08CS (lemma-summands-perfect)
(blueprint: lem-pc-perfect-summand). -/
theorem perfect_of_directSum
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L M : schemeDerivedCategory X)
    (h : Nonempty (K ≅ L ⊞ M))
    (hK : IsPerfect X K) :
    IsPerfect X L ∧ IsPerfect X M := by
  sorry

end AlgebraicGeometry.Scheme
