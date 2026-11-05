/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedPointsFiberProduct
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethLocal
public import WeilConjectures.TraceFormula.Specialization.GenericVanishing

/-!

# Finite support from vanishing over the generic points of coordinate lines

Let `Y` be a scheme of finite type over a field `k` and `C` a bounded constructible
`ℚ̄_ℓ`-complex on `Y`. Suppose that every point of `Y` has an open neighbourhood `U` with finitely
many *coordinates* `bᵢ : U ⟶ 𝔸¹_k`, jointly detecting closed points (a point of `U` all of whose
coordinates are closed points is closed, as for the components of a quasi-finite map
`U ⟶ 𝔸ⁿ_k`), such that `C|_U` vanishes over the generic point of each coordinate line. Then `C`
is supported on finitely many closed points
(`ProEtale.CondensedRing.exists_finset_isZero_of_forall_exists_coordinates`).

This is the assembly of the finite-support step of Gabber's Künneth formula for nearby cycles
(blueprint `sk-prop-tf-nearby-external-kunneth`, "Finite support"): by
`ProEtale.CondensedRing.exists_finset_isZero_leftDerivedUpperStar_of_isZero_pullback`, `C|_U`
vanishes away from the preimage `bᵢ⁻¹(Fᵢ)` of a finite set `Fᵢ` of closed points of the line; the
support of `C|_U` is contained in `⋂ᵢ bᵢ⁻¹(Fᵢ)`, a closed set of closed points of `U`, hence finite;
and finitely many such neighbourhoods cover `Y`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable {k : Type u} [Field k]

end AlgebraicGeometry.ProEtale.CondensedRing
