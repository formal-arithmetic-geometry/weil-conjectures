/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.TraceFormula.CompactCohomology
public import WeilConjectures.TraceFormula.OpenPieceCoherence
public import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
public import WeilConjectures.TraceFormula.CompactPullbackShift

/-!

# The Frobenius endomorphisms of the open–closed localization triangle

Let `Φ` be a finite universal homeomorphism of `X`, `j : U ⟶ X` an open immersion and
`i : Z ⟶ X` a closed immersion onto the complement, both stable under `Φ`. For a Weil object
`(K, φ)` this file defines the endomorphisms `E_U` and `E_Z` of `RΓ_c(X, Rj_! Lj^* K)` and
`RΓ_c(X, Ri_* Li^* K)` induced by the compactly supported Frobenii of `K|_U` and `K|_Z`, and shows
that they are compatible with the counit `Rj_! Lj^* K ⟶ K` and the unit `K ⟶ Ri_* Li^* K` of the
localization triangle (blueprint `prop-trf-trace-additivity-open-closed`,
`sk-i-global-additivity`).

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobeniusOpenPiece`: the operator `E_U`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobeniusClosedPiece`: the operator
  `E_Z`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Adjunction

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X) [IsClosedImmersion i.left]

variable (ℓ) in
/-- The adjunction `Rj_! ⊣ Lj^*` of an open immersion: the adjunction `Rj_! ⊣ Rj^!` transported
along `Rj^! ≅ Lj^*`. -/
noncomputable def boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl :
    boundedConstructibleLowerShriek ℓ j ⊣
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  (boundedConstructibleUpperShriekAdjunction ℓ j).ofNatIsoRight
    (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)

end Adjunction

/-! ### The Frobenius endomorphisms of the triangle -/

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
