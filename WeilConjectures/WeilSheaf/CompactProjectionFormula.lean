/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula

/-!
# The compact-support projection formula for Weil complexes

For a separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type,
the projection formula `Rf₀! M ⊗ T ≅ Rf₀!(M ⊗ f^* T)` for Weil complexes, natural in `M` and `T`,
the tensor product being the native derived tensor product of pro-étale Weil sheaves restricted
to Weil complexes (`AlgebraicGeometry.WeilComplex.nativeConstructibleTensor`), and the two sides
being `AlgebraicGeometry.WeilComplex.nativeCompactProjectionLeft` and
`AlgebraicGeometry.WeilComplex.nativeCompactProjectionRight`.

This is the Weil stage of `fix-prop-projection-formula` (with the definitions of
`lem-sf-derived-weil-compact-projection-formula`). It belongs to the chapter on the six
operations and is not yet formalized there: it is stated here with `sorry`, as an input of the
Verdier exchange `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- **The compact-support projection formula for Weil complexes** (blueprint:
`fix-prop-projection-formula`, for `Λ = ℚ̄_ℓ` with Weil structures, on the native derived Weil
category of `lem-sf-derived-weil-compact-projection-formula`): for a separated morphism of finite
type `f : X ⟶ Y` of separated `k₀`-schemes of finite type,
`Rf₀! M ⊗ T ≅ Rf₀!(M ⊗ f^* T)`, naturally in the Weil complexes `M` on `X` and `T` on `Y`.

This input of the chapter on the six operations is not formalized yet; it is stated with `sorry`
(cross-section rule). -/
theorem nonempty_nativeCompactProjectionLeft_iso :
    Nonempty (nativeCompactProjectionLeft k₀ l f ≅ nativeCompactProjectionRight k₀ l f) :=
  sorry

end WeilComplex

end AlgebraicGeometry
