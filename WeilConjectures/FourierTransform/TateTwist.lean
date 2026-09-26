/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!

# The Tate twist — placeholder, `TODO(unify)`: `def:wf-tate-twist`

The *Tate twist* `K ↦ K(n)` on the derived category of étale sheaves is tensoring with the
`n`-th power of the Tate object, the coefficient sheaf `Λ(1) = lim μ_{ℓᵐ} ⊗ Λ`. It is a
normalization of the coefficients: no weight theory enters, and `K(n)` is abstractly
isomorphic to `K` once a root of unity is chosen.

## Main definitions

- `AlgebraicGeometry.Etale.tateTwist`: the Tate twist `K ↦ K(n)`.

## Implementation notes

The Tate twist belongs to the weight foundations of the blueprint (`def:wf-tate-twist`),
which are formalised in another block. It is stated here, with a `sorry` body, only because
the Fourier–Deligne inversion theorem cannot be written down without it. The file
deliberately lives in the Fourier–Deligne directory rather than in the shared
`WeilConjectures/SixFunctors/Etale/` tree, so that unifying it with the weight foundations
is a rename inside this block rather than a duplicate declaration in a file that every
other block imports.

-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

-- TODO(unify): def:wf-tate-twist
/-- The Tate twist `K ↦ K(n)` on the derived category of `A`-valued étale sheaves on `X`:
the derived tensor product with the `n`-th tensor power of the Tate object `Λ(1)`. -/
noncomputable def tateTwist (X : Scheme.{u}) (n : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  sorry

end AlgebraicGeometry.Etale
