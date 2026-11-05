/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing

/-!
# Bounded morphisms out of `Dctf(X, Λ)` without generic finiteness

Every object of `Dctf(X_ét, Λ)` is compact with bounded morphisms
(`AlgebraicGeometry.Etale.compactBoundedHom_of_constructibleFiniteTor_of_generation`), and every
object of `Dctf(X_proét, Λ)` admits `N` with `Hom(C, L) = 0` for `L` of étale-origin cohomology in
degrees `≤ N`
(`ProEtale.DerivedCategory.exists_forall_eq_zero_of_constructibleFiniteTor_of_generation`).

These restate `AlgebraicGeometry.Etale.compactBoundedHom_of_constructibleFiniteTor` and
`AlgebraicGeometry.ProEtale.DerivedCategory.exists_forall_eq_zero_of_constructibleFiniteTor`
with the same proofs, except that the reduction to the generators `Rg_* Rj_! L` uses only the
generation statement
`AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek`
(`Dctf ⊆` thick envelope of the generators), and the invertibility of the exponent of `Λ` is not
assumed. The converse inclusion, that the generators lie in
`Dctf`, rests on Deligne's generic finiteness (`AlgebraicGeometry.Etale.smoothGenericDirectImage`)
and is not needed here.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme _root_.DerivedCategory

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

end Etale

namespace ProEtale.DerivedCategory

open _root_.DerivedCategory.TStructure

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  {X : Scheme.{u}} (hk : Etale.HasFiniteCohomologicalDimension Λ (Spec (.of k)))
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [QuasiSeparated aX]

end ProEtale.DerivedCategory

end AlgebraicGeometry
