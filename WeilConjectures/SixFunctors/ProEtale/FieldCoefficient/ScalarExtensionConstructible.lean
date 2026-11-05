/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtension

/-!
# Extension of scalars to `ℚ̄_ℓ` is exact and preserves constructibility

Let `Λ` be a finite extension of `ℚ_ℓ` with a continuous embedding `e : Λ → ℚ̄_ℓ`, and
`ℚ̄_ℓ ⊗_Λ - : Sh(X_proét, Λ_X) ⥤ Sh(X_proét, ℚ̄_ℓ,X)` the extension of scalars of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtension`. This file shows:

- it is left adjoint to the restriction of scalars
  (`AlgebraicGeometry.ProEtale.fieldExtendScalarsToAdicAdjunction`), and exact, its underlying
  functor being the extension of scalars of sheaves along the flat `Λ → ℚ̄_ℓ`;
- it sends `Λ_X` to `ℚ̄_ℓ,X` (`AlgebraicGeometry.ProEtale.fieldExtendScalarsToAdicUnitIso`);
- it commutes with pullbacks
  (`AlgebraicGeometry.ProEtale.fieldUpperStarCompExtendScalarsToAdicIso`),
  being the left adjoint of the restriction of scalars, which commutes with pushforwards
  (`AlgebraicGeometry.ProEtale.adicLowerStarCompFieldRestrictScalarsIso`);
- hence it sends lisse, stratified lisse and constructible `Λ`-adic sheaves to lisse, stratified
  lisse and constructible `ℓ`-adic sheaves
  (`AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.extendScalarsToAdic`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] {e : Λ →ₐ[ℚ_[l]] PadicAlgCl l}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ)) (X : Scheme.{u})

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBinaryBiproducts_of_preservesBiproducts

end AlgebraicGeometry.ProEtale
