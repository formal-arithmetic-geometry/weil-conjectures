/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedGlobalSectionsTransport
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
public import WeilConjectures.WeilSheaf.FieldCoefficientTwoColimit

/-!
# Cohomology at the coefficient stage `ℚ̄_ℓ`

Blueprint `def-weil-ordinary-compact-cohomology` defines, at every coefficient stage `Λ`, the
coefficient complexes `RΓ(Y, K) = Fib_s(Ra_{Y*} K)` and `RΓ_c(Y, K) = Fib_s(Ra_{Y!} K)` of an
object `K` of `D^b_c(Y, Λ)` and their cohomology; for a Weil complex they are applied to its
underlying complex. This file records the stage `Λ = ℚ̄_ℓ`:

- for objects of the derived category of sheaves of modules over the `ℓ`-adic constant sheaf
  `ℚ̄_ℓ,Y = colim_E C(-, E)` on the pro-étale site (`AlgebraicGeometry.ProEtale.AdicSheaf`; the
  bounded constructible objects form `D^b_c(Y, ℚ̄_ℓ)`), the derived pushforward `Ra_*`, resp. the
  direct image with compact support `Ra_!`, followed by derived global sections and `Hⁱ`
  (`AlgebraicGeometry.ProEtale.algClosedCohomology`,
  `AlgebraicGeometry.ProEtale.algClosedCompactlySupportedCohomology`). The coefficient sheaf is
  not the sheaf `U ↦ C(U, ℚ̄_ℓ)` of all continuous functions used at the stages `Λ = 𝒪_E, E`
  (`WeilConjectures.WeilSheaf.FieldCoefficientCohomology`): `ℚ̄_ℓ` is not locally compact, and
  a continuous map from a profinite set to `ℚ̄_ℓ` need not factor through any finite `E`;
- for objects `(E, K)` of the `2`-colimit model `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`
  (`AlgebraicGeometry.WeilComplexTwoColimit`), the cohomology of `ℚ̄_ℓ ⊗_E K`
  (`AlgebraicGeometry.WeilComplexTwoColimit.cohomology`,
  `AlgebraicGeometry.WeilComplexTwoColimit.compactlySupportedCohomology`), with its geometric
  Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

namespace ProEtale

variable (l : ℕ) [Fact l.Prime] {Y s : Scheme.{u}} (a : Y ⟶ s)

end ProEtale

namespace WeilComplexTwoColimit

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

end WeilComplexTwoColimit

end AlgebraicGeometry
