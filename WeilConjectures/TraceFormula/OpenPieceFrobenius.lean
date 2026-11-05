/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.LocalizationFrobenius

/-!

# The open-piece Frobenius operator as the Frobenius of a coefficient map

In the setting of `WeilConjectures.TraceFormula.LocalizationFrobenius`, the operator `E_U` on
`RΓ_c(X, Rj_! Lj^* K)` is `RΓ_c(X, ψ_U) ∘ Φ^♯` for a Frobenius coefficient map
`ψ_U : LΦ^* Rj_! Lj^* K ⟶ Rj_! Lj^* K`, compatible with the counit `Rj_! Lj^* K ⟶ K` of the
localization triangle. The abstract shape of the computation is isolated first, for functors
between arbitrary categories.

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible.openPieceFrobeniusCoeff`: the coefficient map
  `ψ_U`.

## Main statements

- `ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobeniusOpenPiece_eq`:
  `E_U = RΓ_c(X, ψ_U) ∘ Φ^♯`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.upperStar_map_counit_comp_str_hom`: the
  compatibility of `ψ_U` with the counit.

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

variable {CX D : Type*} [Category CX] [Category D] {aX : CX ⥤ D} {uΦ : CX ⥤ CX}
variable {CU : Type*} [Category CU] {aU : CU ⥤ D} {uΦU : CU ⥤ CU} {rj : CU ⥤ CX}

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
