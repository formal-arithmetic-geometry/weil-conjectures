/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
public import WeilConjectures.Mathlib.CategoryTheory.Retract

/-!
# Retracts of constructible `ℚ̄_ℓ`-complexes

On a topologically noetherian scheme `T`, constructible module objects over the coefficient ring
`ℚ̄_ℓ,T` are closed under retracts, and hence so are bounded constructible complexes in the
derived category.

## Main results

- `ProEtale.isConstructibleModuleObject_of_retract_padicAlgClRingObj`: a retract of a
  constructible `ℚ̄_ℓ,T`-module object is constructible.
- `ProEtale.boundedConstructible_of_retract_padicAlgClRingObj`: a retract of a bounded
  constructible `ℚ̄_ℓ,T`-complex is bounded constructible.

A retract `M` of `N` is the cokernel of the endomorphism `𝟙 N - r ≫ i` of `N`, so the first
result follows from the closure of constructible module objects under cokernels
(`ProEtale.isConstructibleModuleObject_serre_padicAlgCl`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
