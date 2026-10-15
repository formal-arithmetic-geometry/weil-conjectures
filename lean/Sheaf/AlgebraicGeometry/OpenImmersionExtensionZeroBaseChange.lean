/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import Mathlib.Algebra.Homology.Additive
import Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Exact extension by zero and arbitrary base change

Source: Stacks Project, Etale Cohomology, Proposition 59.70.3 (Tag 03S5) and
Lemma 59.70.5 (Tag 03S6)
(blueprint: sbc-prop-extension-by-zero-and-arbitrary-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Extension by zero of abelian etale sheaves is exact and commutes with arbitrary
base change, also on unbounded cochain complexes. The canonical comparison is written
in the mate direction; its inverse is the displayed comparison in the blueprint.
Source: Stacks Project, Tags 03S5 and 03S6
(blueprint: sbc-prop-extension-by-zero-and-arbitrary-base-change).

Proof:
1. Extension by zero is additive and preserves short exact sequences by
lem-weil-pbc-extension-by-zero-exact (Stacks 03DJ, specialized in 03S5).
2. The canonical mate for the Cartesian square is invertible by
lem-weil-pbc-etale-shriek-base-change-modules (03S6), specialized to abelian sheaves.
Invert it to obtain a^{-1} j_! F → j'_! a_U^{-1} F, naturally in F.
3. Apply the additive functors degreewise. Naturality of the sheaf comparison for
each differential makes its components a chain map, and the same calculation for
the inverses gives its inverse chain map. Exactness degreewise gives exactness on
complexes; in particular extension by zero preserves acyclic complexes and
quasi-isomorphisms. There is no boundedness assumption. -/
theorem openImmersionExtensionZero_exact_baseChange
    {U Z Z' : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] (a : Z' ⟶ Z) :
    (openImmersionLowerShriek AddCommGrpCat.{u + 1} j).Additive ∧
    PreservesFiniteLimits (openImmersionLowerShriek AddCommGrpCat.{u + 1} j) ∧
    PreservesFiniteColimits (openImmersionLowerShriek AddCommGrpCat.{u + 1} j) ∧
    IsIso (openImmersionLowerShriekBaseChangeMap AddCommGrpCat.{u + 1}
      (IsPullback.of_hasPullback a j).flip.toCommSq) ∧
    IsIso ((openImmersionLowerShriekBaseChangeMap AddCommGrpCat.{u + 1}
      (IsPullback.of_hasPullback a j).flip.toCommSq).mapHomologicalComplex
        (ComplexShape.up ℤ)) := by
  sorry

end AlgebraicGeometry.Etale
