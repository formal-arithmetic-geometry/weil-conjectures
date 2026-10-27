/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Mathlib.Algebra.Field.Defs

/-!
# The largest schematic open of an algebraic space over a field

Source: Stacks Project, Properties of Spaces, Tag 03JH (`lemma-subscheme`),
over the base `Spec k` (blueprint: lem-sfb-space-dense-schematic-locus).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space over a field has a largest open subspace represented by a scheme.
No separation, finite-type, quasi-compactness or nonemptiness assumption is imposed.

Source: Stacks Project, Properties of Spaces, Tag 03JH (`lemma-subscheme`),
over the base `Spec k` (blueprint: lem-sfb-space-dense-schematic-locus).

Proof: put `S = Spec k` and apply `lem-sfb-space-largest-schematic-open` to `X`.
It gives an open subspace represented by an `S`-scheme and containing every such
schematic open. Since the sheaves are on the big fppf site of schemes over `S`,
a representing object is precisely a scheme over `S`. Thus its representability
and maximality give the two required clauses. The general theorem imposes no
separation or quasi-compactness hypothesis and allows the empty open subspace. -/
theorem exists_largest_schematic_open_over_field (k : Type u) [Field k]
    (X : AlgebraicSpace (Spec (.of k))) :
    ∃ U : OpenSubspace X, U.val.toFunctor.IsRepresentable ∧
      ∀ V : OpenSubspace X, V.val.toFunctor.IsRepresentable → V ≤ U := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
