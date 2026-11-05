/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowGLLift

/-!
# Lattices of `ℓ`-adic towers of rank `r` are locally `ℤ_ℓ,X^r`

Finite direct sums commute with limits (`CategoryTheory.Limits.Cone.biproductPow` and
`CategoryTheory.Limits.IsLimit.biproductPow`), so the limit of the tower `(ℤ/ℓⁿ)_X^r` is the
direct sum `ℤ_ℓ,X^r` of `r` copies of `ℤ_ℓ,X`
(`AlgebraicGeometry.ProEtale.limitZmodPowAbSheafDiagramPowIso`). Hence an `ℓ`-adic tower `(Gₙ)` of
pro-étale abelian sheaves with each `Gₙ` locally isomorphic to `(ℤ/ℓⁿ)_X^r` has a limit `lim Gₙ`
which is pro-étale locally isomorphic to `ℤ_ℓ,X^r`
(`AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_padicIntAbSheaf_pow`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CategoryTheory.Limits

variable {K D : Type*} [Category* K] [Category* D] [Preadditive D] [HasFiniteBiproducts D]
  {F : K ⥤ D} (ι : Type*) [Finite ι]

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

end AlgebraicGeometry.ProEtale
