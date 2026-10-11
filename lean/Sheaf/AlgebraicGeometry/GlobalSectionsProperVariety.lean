/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF stage-2 worker K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.Variety
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-!
# Global sections of a proper variety

Source: Stacks Project, Varieties, Tag 04L2 (blueprint: lem-pc-h0-proper-variety).

## Main statements

* `AlgebraicGeometry.globalSections_finite_field_of_isVariety` states the node's first clause:
  the global sections of a proper variety form a finite field extension.

The node's second clause (a proper geometrically integral scheme has `H⁰(X, 𝒪_X) = k`) is
stated by the source as `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyIntegral`
(`WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective`), recorded next to this module's
declaration and not stated again here.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- For a proper variety over a field, global sections are a finite field extension.

Source: Stacks Project, Varieties, Tag 04L2, clause (1)
(blueprint: lem-pc-h0-proper-variety).

Put `A = H⁰(X, 𝒪_X)`. Properness and the finite-dimensionality clause of
`lem-pc-euler-characteristic-well-defined` make `A` finite-dimensional over `k`.
The variety hypothesis (`def-pc-curve`) makes `X` integral. Restriction to its
generic point embeds `A` into the function field by
`lem-sc-integral-scheme-stalks-in-function-field`, so `A` is a domain. Apply
`lem-weil-pbc-finite-dimensional-domain-is-field` to obtain the field structure.
-/
theorem globalSections_finite_field_of_isVariety [IsProper (X ↘ Spec (.of k))]
    [Scheme.Hom.IsVariety (X ↘ Spec (.of k))] :
    (Scheme.globalSectionsRingHom k (X := X)).Finite ∧ IsField Γ(X, ⊤) := by
  sorry

end AlgebraicGeometry
