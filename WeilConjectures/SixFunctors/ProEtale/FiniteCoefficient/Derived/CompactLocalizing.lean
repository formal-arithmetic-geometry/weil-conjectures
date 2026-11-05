/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.Triangulated.CompactFamily
public import WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-!
# Objects of `Dctf(X, Λ)` are compact in `Loc(Dctf(X, Λ))`

Blueprint `det-ctf-finite-compact-proetale`. Let `k` be a field of finite cohomological dimension
for `Λ`-modules, `X` a finite-type `k`-scheme and `Λ` a finite ring whose exponent is invertible
on `X`. Every object `C` of `Dctf(X, Λ)` is compact in `Loc(Dctf(X, Λ))`
(`AlgebraicGeometry.ProEtale.DerivedCategory.isCompactObj_of_constructibleFiniteTor`).

Write `C = ν^* C'` with `C'` in `Dctf(X_ét, Λ)`, which is compact with bounded morphisms in
`D(X_ét, Λ)` (`AlgebraicGeometry.Etale.compactBoundedHom_of_constructibleFiniteTor`). Morphisms
from `C` to an object `Y` with cohomology sheaves of étale origin (a class containing
`Loc(Dctf(X, Λ))`) only depend on the truncation `τ_{[N, m]} Y` for suitable `N ≤ m`:

* `Hom(C, L) = 0` for `L` of étale-origin cohomology in degrees `≤ N`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.exists_forall_eq_zero_of_constructibleFiniteTor`):
  `L` is the homotopy limit of its bounded truncations (left completeness of `D(X_proét)`), and
  `Hom(ν^* C', ν^* G) = Hom(C', G)` for bounded `G`;
* `Hom(C, Z) = 0` for `Z` in degrees `> m`, since `C` is bounded above.

On uniformly bounded families of étale origin, `ν^*` identifies the morphisms out of `C` with the
étale ones, where `C'` is compact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme _root_.DerivedCategory.TStructure

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  {X : Scheme.{u}} (hk : Etale.HasFiniteCohomologicalDimension Λ (Spec (.of k)))
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [QuasiSeparated aX]
  [HasInvertibleExponent Λ X]

namespace DerivedCategory

end DerivedCategory

end AlgebraicGeometry.ProEtale
