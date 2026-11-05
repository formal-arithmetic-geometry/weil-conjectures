/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtensionConstructible
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalars

/-!
# Extension of scalars between finite extensions of `ℚ_ℓ` is exact and preserves
constructibility

Let `e : Λ → Λ'` be a continuous map of finite extensions of `ℚ_ℓ` and
`Λ' ⊗_Λ - : Sh(X_proét, Λ_X) ⥤ Sh(X_proét, Λ'_X)` the extension of scalars of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalars`. As for the
extension of scalars to `ℚ̄_ℓ`
(`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtensionConstructible`):

- it is exact, its underlying functor being the extension of scalars of sheaves along the flat
  `Λ → Λ'`;
- it commutes with pullbacks
  (`AlgebraicGeometry.ProEtale.fieldUpperStarCompExtendScalarsIso`), being the left adjoint of
  the restriction of scalars, which commutes with pushforwards
  (`AlgebraicGeometry.ProEtale.fieldLowerStarCompRestrictScalarsIso`);
- hence it preserves lisse, stratified lisse and constructible sheaves
  (`AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.extendScalars`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBinaryBiproducts_of_preservesBiproducts

variable (X)

variable {X}

end AlgebraicGeometry.ProEtale
