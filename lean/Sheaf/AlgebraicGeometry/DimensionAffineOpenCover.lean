/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.AlgebraicGeometry.Dimension
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Dimension from an affine open cover

Source: Stacks Project, Properties, Lemma 04MU; Schemes, Lemma 01HV;
Algebra, Lemma 00KG (blueprint: lem-pc-dimension-affine-open-cover).
-/

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- (blueprint: lem-pc-dimension-affine-open-cover) Let the nonempty scheme `X` be covered by
open subschemes `U i`, each isomorphic to the spectrum of the commutative ring `A i`.
Its dimension, defined as the supremum of the Krull dimensions of its local rings, is the
supremum of the Krull dimensions of these rings (Stacks, Tags 04MU, 01HV, 00KG).

Proof: For each chart, the scheme isomorphism identifies its ring of global sections with
`A i`, hence their Krull dimensions agree. The points of the chart correspond bijectively
to primes of its ring of sections. The stalk at each point is the localization at the
corresponding prime, whose dimension is the height of that prime. Taking the supremum over
the chart gives its ring dimension by the supremum-of-heights formula, including the empty
chart, whose ring has dimension bottom. Finally, the opens cover `X`, so regroup the
supremum of local-ring dimensions over all points by charts. -/
theorem Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover
    (X : Scheme.{u}) [Nonempty X] {I : Type v} (U : I → X.Opens)
    (hcover : ⨆ i, U i = ⊤) (A : I → CommRingCat.{u})
    (hiso : ∀ i, (U i : Scheme.{u}) ≅ Spec (A i)) :
    X.dim = ⨆ i, ringKrullDim (A i) := by
  sorry

end AlgebraicGeometry
