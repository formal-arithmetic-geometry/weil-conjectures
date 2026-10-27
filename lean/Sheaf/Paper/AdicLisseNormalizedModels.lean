/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.Paper.AdicLisseCalculusData

/-! # Normalized realization, cohomology and fibres of adic lisse systems

Source: Bhatt--Scholze 6.8.4, 6.8.11 and 6.8.14.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Qbar : Type (u + 1)) [Field Qbar]
  [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar] (X : Scheme.{u})
  [IsNoetherian X] [X.IsSeparated]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]


/-- The normalized coefficient models, before any tensor or dual comparison.
Source: Bhatt--Scholze, Propositions 6.8.4(1),(4), 6.8.11(3), and 6.8.14(2).
(blueprint: lem-per-adic-lisse-normalized-models).

Proof: identify the two completed coefficient presentations by the ring-sheaf
isomorphism fixed by every finite quotient projection. Exact restriction along
this isomorphism identifies the three bounded-constructible-complete conditions.
It therefore restricts to the integral categories. Extend on pure tensors to the
raw rational localizations. The canonical scalar comparisons, with their unit
and tower equations, descend these equivalences to common finite coefficient
fields, giving comparison and comparison_integral.

At a finite coefficient field take the actual inverse limit of the finite etale
levels transported to the pro-etale site. On a finite stratification it has finite
integral module models. The completed-system comparison and the stratified-perfect
criterion put its degree-zero complex in the integral category. These constructions
are functorial in compatible systems and commute with finite scalar extension.
Rationalizing the maps sends a pure tensor a tensor f to a times the realized map
of f. Descend through the coefficient cocartesian localization; this gives exactly
the realization_integral and realization_map equations.

The integral standard truncations preserve the integral category. Rationalization
is t-exact, and finite coefficient extension is finite free and hence t-exact.
Uniqueness of standard truncation comparisons gives their natural, coherent
coefficient-change maps. Descend shift followed by degree-zero cohomology to the
common-stage category. This gives cohomology_integral. The inverse-limit complexes
above are in degree zero, so their zero cohomology is themselves and all other
cohomology vanishes. Rationalization preserves these assertions.

Finally use completed geometric pullback, the fixed coefficient transport,
degree-zero cohomology and point sections. Quotient-normalized pullback and point
sections commute with finite coefficient extension. Extend scalars to Qbar and
descend the resulting functors and comparison isomorphisms. On a normalized lisse
system, compute sections by finite etale fibres and their inverse limit; the
finite-module adic limit comparison identifies this with the recorded adic fibre
functor. Naturality holds on integral maps and pure rational tensors, and the
coefficient-change equations give naturality on the localization generators.
All constructions allow zero modules, empty schemes and varying component ranks. -/
theorem adic_lisse_normalized_models :
    Nonempty (AdicLisseCalculusModels l Qbar X) := by sorry

end AlgebraicGeometry.Scheme
