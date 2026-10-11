/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.Dimension
public import Sheaf.AlgebraicGeometry.Morphisms.Projective

/-!
# Projectivity of proper schemes of dimension at most one

Source: Stacks Project, Varieties, Lemma 33.43.4 (Tag 0A26)
(blueprint: lem-sc-proper-dim-one-projective).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper scheme over a field with dimension at most one is projective, including the empty
scheme, whose dimension is `⊥`. Here projectivity uses the blueprint's H-projective convention:
a closed immersion into a finite-dimensional projective space, together with quasi-compactness.
Source: Stacks Project, Varieties, Lemma 33.43.4 (Tag 0A26)
(blueprint: lem-sc-proper-dim-one-projective).

Proof, step 1: properness gives separatedness and finite type (def-weil-proper-morphism).
Apply lem-sc-dim-one-quasi-projective to obtain an immersion into projective space over the
field. The dimension used here agrees with topological Krull dimension by
`Scheme.dim_eq_topologicalKrullDim`.
Step 2: projective space is separated over the field
(lem-weil-pbc-projective-space-proj-separated). Since the composite is proper, the immersion is
proper by lem-weil-pbc-proper-over-separated. Its image is closed by
lem-weil-pbc-proper-closed-image; an immersion with closed image is a closed immersion by
lem-weil-pbc-immersion-closed-image-closed-immersion. This gives H-projectivity, and properness
already supplies quasi-compactness, hence projectivity (def-pc-projective-morphism). -/
theorem isProjective_of_isProper_of_dim_le_one {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : X.dim ≤ 1) : IsProjective f := by
  sorry

end AlgebraicGeometry
