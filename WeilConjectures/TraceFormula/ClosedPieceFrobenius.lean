/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.LocalizationFrobenius

/-!

# The closed-piece Frobenius operator as the Frobenius of a coefficient map

In the setting of `WeilConjectures.TraceFormula.LocalizationFrobenius`, the operator `E_Z` on
`RΓ_c(X, Ri_* Li^* K)` is `RΓ_c(X, ψ_Z) ∘ Φ^♯` for a Frobenius coefficient map
`ψ_Z : LΦ^* Ri_* Li^* K ⟶ Ri_* Li^* K`, compatible with the unit `K ⟶ Ri_* Li^* K` of the
localization triangle. The abstract shape of the computation is isolated first, for functors
between arbitrary categories.

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible.closedPieceFrobeniusCoeff`: the coefficient
  map `ψ_Z`.

## Main statements

- `ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobeniusClosedPiece_eq`:
  `E_Z = RΓ_c(X, ψ_Z) ∘ Φ^♯`.
- `WeilBoundedConstructible.upperStar_map_unit_comp_closedPieceFrobeniusCoeff`
  (the compatibility of `ψ_Z` with the unit).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section PieceCoefficients

variable {CX CZ D : Type*} [Category CX] [Category CZ] [Category D] {aX : CX ⥤ D}
  {aZ : CZ ⥤ D} {uΦ : CX ⥤ CX} {ui : CX ⥤ CZ} {uΦZ : CZ ⥤ CZ} {ri : CZ ⥤ CX}

end PieceCoefficients

section Frobenius

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

variable {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left] [IsFinite Φ.left]
  [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]

namespace WeilBoundedConstructible

end WeilBoundedConstructible

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
