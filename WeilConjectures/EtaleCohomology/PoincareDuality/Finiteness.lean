/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.EtaleCohomology.PoincareDuality.Classes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Finiteness: the global sections are perfect at the point

The duality statements pair the cohomology of `X` against itself, so they need that it is
*perfect at the point*: for `K ∈ D^b_{ctf}(X, Λ)`, both `RΓ_c(X, K)` and `RΓ(X, K)` are
bounded with finite cohomology of finite Tor amplitude. This is Deligne's finiteness theorem
(SGA 4½, *Th. finitude*), for `a : X ⟶ Spec k` separated of finite type over a separably closed
field and finite coefficients `Λ` whose exponent is invertible on `Spec k`.

As in `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality`, `RΓ_c(X, K)` and `RΓ(X, K)`
are read one step earlier, as `Ra_! K` and `Ra_* K` in `D(Spec k_ét, Λ)`. "Perfect point
complex" is rendered as dualizability (`CategoryTheory.IsDualizable`), as everywhere in the
project (see `WeilConjectures.SixFunctors.Etale.Derived.Perfect`). The boundedness and finiteness
of the cohomology modules then follow from the corresponding facts at the point,
`AlgebraicGeometry.Etale.exists_subsingleton_shiftedHom_of_isDualizable` and
`AlgebraicGeometry.Etale.finite_shiftedHom_of_isDualizable`.

## Main statements

- `AlgebraicGeometry.Etale.isDualizable_rightDerivedLowerShriek`,
  `AlgebraicGeometry.Etale.isDualizable_rightDerivedLowerStar` (`sk-lem-finite`): `RΓ_c(X, K)`
  and `RΓ(X, K)` are perfect point complexes.
- `AlgebraicGeometry.Etale.exists_subsingleton_shiftedHom_rightDerivedLowerShriek`,
  `AlgebraicGeometry.Etale.exists_subsingleton_shiftedHom_rightDerivedLowerStar`:
  `H^q_c(X, K)` and `H^q(X, K)` vanish outside a bounded range of degrees.
- `AlgebraicGeometry.Etale.finite_shiftedHom_rightDerivedLowerShriek`,
  `AlgebraicGeometry.Etale.finite_shiftedHom_rightDerivedLowerStar`: they are finite
  `Λ`-modules.

## Implementation notes

The coefficient stages of the blueprint are `A_{E,n}`, `𝒪_E`, `E` and `ℚ̄_ℓ`. The statements
here are at the finite stages, `ModuleCat Λ` with `[Finite Λ]`. At the stage `𝒪_E`, the
preservation of derived completeness by `Ra_!` and `Ra_*` is stated in
`WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete`. *Not stated*: the common Tor
amplitude of the reductions over `𝒪_E`, the finite-dimensionality over `E` (the `E` stage
`DerivedCategoryDerivedCompleteRational` carries no `Rf_!`), and the `ℚ̄_ℓ` stage, which does
not exist in the repository.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X : Scheme.{u}} {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  (a : X ⟶ Spec (.of k)) [QuasiCompact a]
  {K : DerivedCategoryModule Λ X} (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)

section LowerShriek

variable [HasCompactification a]

include hK in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ_c(X, K)` is a perfect point complex.** For `a : X ⟶ Spec k` separated of finite type and
`K ∈ D^b_{ctf}(X, Λ)`, the compactly supported direct image `Ra_! K` is dualizable in
`D(Spec k_ét, Λ)`. Its dual is then dualizable too, by
`AlgebraicGeometry.Etale.DerivedCategory.isDualizable_coefficientDual`. -/
theorem isDualizable_rightDerivedLowerShriek :
    IsDualizable ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) :=
  sorry

include hK in
/-- **Boundedness of compactly supported cohomology.** For `K ∈ D^b_{ctf}(X, Λ)`, the
cohomology `H^q_c(X, K)`, the degree `q` classes of `Ra_! K`, vanishes for `q` outside a bounded
range `[m, n]`. Compare `AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`. -/
theorem exists_subsingleton_shiftedHom_rightDerivedLowerShriek :
    ∃ m n : ℤ, ∀ q : ℤ, q < m ∨ n < q →
      Subsingleton (ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) q) :=
  exists_subsingleton_shiftedHom_of_isDualizable Λ
    (isDualizable_rightDerivedLowerShriek Λ a hK)

include hK in
/-- **Finiteness of compactly supported cohomology.** For `K ∈ D^b_{ctf}(X, Λ)` every
cohomology module `H^q_c(X, K)`, the degree `q` classes of `Ra_! K`, is a finite `Λ`-module.
Compare `AlgebraicGeometry.Etale.finite_compactlySupportedCohomology`. -/
theorem finite_shiftedHom_rightDerivedLowerShriek (q : ℤ) :
    Module.Finite Λ (ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) q) :=
  finite_shiftedHom_of_isDualizable Λ (isDualizable_rightDerivedLowerShriek Λ a hK) q

end LowerShriek

section LowerStar

variable [IsSeparated a] [LocallyOfFiniteType a]

include hK in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ(X, K)` is a perfect point complex.** For `a : X ⟶ Spec k` separated of finite type and
`K ∈ D^b_{ctf}(X, Λ)`, the direct image `Ra_* K` is dualizable in `D(Spec k_ét, Λ)`. Its dual
is then dualizable too, by `AlgebraicGeometry.Etale.DerivedCategory.isDualizable_coefficientDual`.
-/
theorem isDualizable_rightDerivedLowerStar :
    IsDualizable ((R((a)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

include hK in
/-- **Boundedness of ordinary cohomology.** For `K ∈ D^b_{ctf}(X, Λ)`, the cohomology
`H^q(X, K)`, the degree `q` classes of `Ra_* K`, vanishes for `q` outside a bounded range
`[m, n]`. -/
theorem exists_subsingleton_shiftedHom_rightDerivedLowerStar :
    ∃ m n : ℤ, ∀ q : ℤ, q < m ∨ n < q →
      Subsingleton (ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj K) q) :=
  exists_subsingleton_shiftedHom_of_isDualizable Λ
    (isDualizable_rightDerivedLowerStar Λ a hK)

include hK in
/-- **Finiteness of ordinary cohomology.** For `K ∈ D^b_{ctf}(X, Λ)` every cohomology module
`H^q(X, K)`, the degree `q` classes of `Ra_* K`, is a finite `Λ`-module. -/
theorem finite_shiftedHom_rightDerivedLowerStar (q : ℤ) :
    Module.Finite Λ (ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj K) q) :=
  finite_shiftedHom_of_isDualizable Λ (isDualizable_rightDerivedLowerStar Λ a hK) q

end LowerStar

end Etale

end AlgebraicGeometry
