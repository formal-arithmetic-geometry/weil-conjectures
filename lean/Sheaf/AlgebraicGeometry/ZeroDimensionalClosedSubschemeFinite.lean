/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.KrullDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Zero-dimensional closed subschemes are finite over the base field

Source: Stacks Project, Varieties, Tag 06LH (Lemma algebraic-scheme-dim-0), algebraic case;
Morphisms, Tag 03J3, opening paragraph
(blueprint: lem-pc-zero-dimensional-closed-subscheme-finite).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed subscheme of a finite-type scheme over a field, with topological dimension
at most zero, is finite over the field and affine, with finite-dimensional global sections.

Source: Stacks Project, Varieties, Tag 06LH (Lemma algebraic-scheme-dim-0), algebraic case;
Morphisms, Tag 03J3, opening paragraph
(blueprint: lem-pc-zero-dimensional-closed-subscheme-finite).

Proof: (1) The closed immersion is proper and hence of finite type
[lem-weil-pbc-closed-immersion-proper]. Composing it with the finite-type structure morphism
makes `Z` finite type over `k` [def-weil-finite-type-morphism].
(2) If `Z` is empty it is the spectrum of the zero ring, so is affine and finite over `k`.
Otherwise [lem-pc-scheme-dimension-local-rings] identifies its topological dimension with
the supremum of local-ring dimensions [def-pc-dimension]. Thus the local-ring dimension
is at most zero, and [lem-pc-algebraic-dim-zero-affine-finite] gives affineness and finiteness.
(3) Apply [lem-weil-pbc-finite-over-field-affine-finite-dim] to the resulting finite
structure morphism: `Z` is the spectrum of its finite-dimensional global-section algebra.
-/
theorem closed_subscheme_finite_of_topologicalKrullDim_le_zero
    {k : Type u} [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] (hZ : topologicalKrullDim Z ≤ 0) :
    IsFinite (i ≫ f) ∧ IsAffine Z ∧
      (letI := (i ≫ f).ΓAlgebra; FiniteDimensional k Γ(Z, ⊤)) := by
  sorry

end AlgebraicGeometry
