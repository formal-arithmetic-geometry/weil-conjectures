/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.PositiveTensorFamily

/-! # Tensor sections and affine nonvanishing loci

Source: Stacks Project, Varieties Lemma 09NC, proof, invoking Properties Lemma 01PV
(blueprint: lem-sc-tensor-section-affine-open).
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The tensor section `τ = t₀ ⊗ ⋯ ⊗ tₙ` of a nonempty finite family of invertible modules
(the landed left-associated `positiveTensorFamily` with its section
`positiveTensorFamilySection`, def-sc-positive-tensor-family; `n` means `n + 1` factors)
has nonvanishing locus equal to the intersection of the factor loci. If one factor locus is
affine, so is this intersection.

Source: Stacks Project, Varieties Lemma 09NC, proof, invoking Properties Lemma 01PV
(blueprint: lem-sc-tensor-section-affine-open).

Proof:
1. By `lem-weil-pbc-invertible-pullback-tensor`, each tensor product is invertible and
   its fibre section is the pure tensor of the factor values. Each factor fibre is
   one-dimensional over the residue field. Choosing bases shows that this tensor is
   nonzero exactly when all factor values are nonzero.
   By `lem-weil-pbc-nonvanishing-section-trivializes`, nonzero fibre value is precisely
   membership in the nonvanishing locus. Induction on the number of factors gives the
   equality.
2. If the `j`-th factor locus is affine, start with that affine open and intersect
   successively with every remaining factor locus. At each step apply
   `lem-sc-affine-cap-section-open` to the invertible factor and its section.
   The resulting affine open is the tensor section locus by step 1.
-/
theorem tensor_section_affine_open {X : Scheme.{u}} (n : ℕ)
    (L : Fin (n + 1) → X.Modules) [∀ i, (L i).IsInvertible]
    (t : (i : Fin (n + 1)) → (L i).sections) :
    (nonvanishingLocus (positiveTensorFamily n L)
        ((positiveTensorFamilySection n L t).val (Opposite.op ⊤)) =
      ⋂ i, nonvanishingLocus (L i) ((t i).val (Opposite.op ⊤))) ∧
    ((∃ j : Fin (n + 1), ∃ U : X.Opens, IsAffineOpen U ∧
        (U : Set X) = nonvanishingLocus (L j) ((t j).val (Opposite.op ⊤))) →
      ∃ U : X.Opens, IsAffineOpen U ∧
        (U : Set X) = nonvanishingLocus (positiveTensorFamily n L)
          ((positiveTensorFamilySection n L t).val (Opposite.op ⊤))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
