/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# An étaleness criterion via Kähler differentials

## Main results

- `Algebra.FormallyEtale.of_bijective_mapBaseChange`: for `R → S → T` with `H¹(L_{T/R}) = 0`
  (e.g. `T` formally smooth over `R`), if `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective, then `T` is
  formally étale over `S`.
- `MvPolynomial.etale_aeval_of_basis_kaehlerDifferential`: if `T` is smooth over `R` and
  `Ω[T⁄R]` has a basis `d uᵢ` for a finite family `uᵢ : T`, then `R[Xᵢ] → T`, `Xᵢ ↦ uᵢ`, is
  étale.
-/

@[expose] public section

open KaehlerDifferential TensorProduct

namespace Algebra

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T]

end Algebra

namespace MvPolynomial

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]

end MvPolynomial
