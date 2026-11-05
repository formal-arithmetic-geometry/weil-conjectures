/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeLocal
public import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowCokernel

/-!
# The tower `(ℤ/ℓⁿ)_X` is `ℓ`-adic

Restricted to any object `Y` of `X_proét`, the transition `(ℤ/ℓⁿ⁺¹)_X ⟶ (ℤ/ℓⁿ)_X` of the tower
of abelian sheaves `n ↦ (ℤ/ℓⁿ)_X` is a cokernel of multiplication by `ℓⁿ`
(`AlgebraicGeometry.ProEtale.exists_isColimit_cokernelCofork_zmodPowAbSheafDiagram`): on
sections, reduction `C(U, ℤ/ℓⁿ⁺¹) ⟶ C(U, ℤ/ℓⁿ)` of locally constant functions is surjective
with kernel `ℓⁿ C(U, ℤ/ℓⁿ⁺¹)`, the values being lifted pointwise, which preserves continuity
as `ℤ/ℓⁿ⁺¹` is discrete.

Hence `lim Gₙ` is locally `ℤ_ℓ,X` for an `ℓ`-adic tower `(Gₙ)` of sheaves locally isomorphic to
`(ℤ/ℓⁿ)_X`, as soon as automorphisms of `(ℤ/ℓⁿ)_X` lift locally to `(ℤ/ℓⁿ⁺¹)_X`
(`AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_padicIntAbSheaf_of_lift_aut`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace ZMod

end ZMod

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

end AlgebraicGeometry.ProEtale
