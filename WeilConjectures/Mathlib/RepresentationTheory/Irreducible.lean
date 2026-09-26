/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RepresentationTheory.Irreducible

@[expose] public section

/-!
# Constituents of a representation

The constituents of a finite-dimensional representation are the irreducible successive
quotients of a composition series, counted with multiplicity; equivalently, by Jordan-Hölder,
the irreducible subquotients. Irreducibility itself is `Representation.IsIrreducible`.

## Main definitions

- `Representation.IsConstituent`
-/

namespace Representation

variable {k G V V' : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']

/-- Blueprint `sk-d-real-operations`: Operations, constituents and coinvariants.

`σ` is a *constituent* of `ρ` if it is irreducible and isomorphic to a subquotient of `ρ`. By
Jordan-Hölder these are exactly the irreducible successive quotients of a composition series
of `ρ`, counted with multiplicity. -/
def IsConstituent (ρ : Representation k G V) (σ : Representation k G V') : Prop :=
  σ.IsIrreducible ∧ ∃ N M : Subrepresentation ρ, N ≤ M ∧
    Nonempty (σ.asModule ≃ₗ[MonoidAlgebra k G]
      (M.asSubmodule ⧸ Submodule.comap M.asSubmodule.subtype N.asSubmodule))

end Representation
