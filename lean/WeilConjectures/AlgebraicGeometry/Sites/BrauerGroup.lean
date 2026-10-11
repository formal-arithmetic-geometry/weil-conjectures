/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.FieldTheory.Cr

/-!
# The Brauer group of a field as étale cohomology

For a field `K` the Brauer group of central simple algebras, `BrauerGroup K`, is in bijection
with the cohomological Brauer group `H²(Spec(K)_ét, 𝔾ₘ)`.

## Main statements

- `AlgebraicGeometry.Scheme.nonempty_equiv_cohomologicalBrauerGroup`:
  `Br(K) ≅ H²(Spec(K)_ét, 𝔾ₘ)`.
- `IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup`: `H²(Spec(K)_ét, 𝔾ₘ) = 0` for a
  quasi-algebraically closed field `K`.

## TODO

`BrauerGroup K` carries no group structure in Mathlib yet, so the comparison is recorded as a
bijection of sets. It should be upgraded to a group isomorphism once the group structure
exists.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- **The Brauer group of a field is `H²(K, 𝔾ₘ)`.** For a field `K` the Brauer group of
central simple `K`-algebras is in bijection with the cohomological Brauer group
`H²(Spec(K)_ét, 𝔾ₘ)`. -/
theorem nonempty_equiv_cohomologicalBrauerGroup (K : Type u) [Field K] :
    Nonempty (BrauerGroup.{u, u} K ≃ (Spec (.of K)).CohomologicalBrauerGroup) :=
  -- Proof sketch: both sides are identified with the Galois cohomology group
  -- `H²(Gal(K^sep/K), (K^sep)ˣ)`, via crossed product algebras resp. the equivalence between
  -- étale sheaves on `Spec K` and discrete `Gal(K^sep/K)`-sets.
  sorry

end AlgebraicGeometry.Scheme

open AlgebraicGeometry

/-- The cohomological Brauer group `H²(Spec(K)_ét, 𝔾ₘ)` of a quasi-algebraically closed field
`K` vanishes.
(blueprint: `sk-prop-tsen`) -/
theorem IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup (K : Type u) [Field K]
    [IsQuasiAlgClosed K] : Subsingleton (Spec (.of K)).CohomologicalBrauerGroup := by
  obtain ⟨e⟩ := Scheme.nonempty_equiv_cohomologicalBrauerGroup K
  have := IsQuasiAlgClosed.subsingleton_brauerGroup K
  exact e.symm.subsingleton
