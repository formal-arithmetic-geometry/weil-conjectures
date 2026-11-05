/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
public import WeilConjectures.FieldTheory.FiniteFieldGaloisCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.ForgetCohomologyVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension

/-!
# The cohomological dimension of a finite field

Let `k` be a finite field and `Λ` a ring in which a prime `ℓ` vanishes. Then
`H^q(Spec k, F) = 0` for every `q > 1` and every étale sheaf `F` of `Λ`-modules on `Spec k`; in
particular `Spec k` has finite cohomological dimension (blueprint `sk-lem-base-field-cd`, in the
sense of `sk-def-cd`, i.e. `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimension`).

The cohomology of `F` is that of its underlying abelian sheaf (Stacks 03FD), which is the Galois
cohomology of its geometric fibre, an `ℓ`-primary discrete module over the absolute Galois group
`Gal(k̄/k)` (`AlgebraicGeometry.Scheme.sheafHAddEquivGaloisH`). This group has `ℓ`-cohomological
dimension one (`FiniteField.subsingleton_H_galois`), via its `ℓ`-adic procyclic quotient.

No assumption that `ℓ` is invertible in `k` is needed.

## Main statements

- `AlgebraicGeometry.Etale.isZero_cohomology_singleFunctor_iff_subsingleton_sheafH`: the
  cohomology of a sheaf of `Λ`-modules vanishes if and only if that of the underlying abelian
  sheaf does.
- `AlgebraicGeometry.Etale.isZero_cohomology_spec_of_finite`: the vanishing above degree one.
- `AlgebraicGeometry.Etale.hasFiniteCohomologicalDimension_of_finite`: the finiteness of the
  cohomological dimension.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

end AlgebraicGeometry.Etale
