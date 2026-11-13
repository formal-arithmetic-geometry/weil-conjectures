/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LocalOperatorUnit
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
public import WeilConjectures.TraceFormula.GrothendieckLefschetz.Finite

/-!
# Point counting with finite coefficients

For the constant sheaf `Λ_X` on the geometric fibre `X = X₀ ×_k k̄` of a separated scheme of
finite type over `k = 𝔽_q`, with its canonical Weil structure `Lg_X^* Λ_X ≅ Λ_X`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`), and a finite ring `Λ` whose exponent is
invertible in `k̄`,
```
tr_Λ(Frob_{X,Λ_X}^m ∣ RΓ_c(X, Λ_X)) = #X₀(𝔽_{q^m}) · 1_Λ
```
for every `m ≥ 1` (for `Λ = ℚ̄_ℓ` this is
`AlgebraicGeometry.ProEtale.CondensedRing.weilPointCount`).

## Implementation details

The formula is deduced from the trace formula
`AlgebraicGeometry.Etale.trace_globalOperator_iterateWeilDatum_eq_finsum` and the normalization
of the local terms of `Λ_X`, `AlgebraicGeometry.Etale.trace_localOperator_unit`, deduced from
`AlgebraicGeometry.Etale.trace_localOperator_leftDerivedUpperStarUnitIso`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  [HasCompactification f.geometricFiberToAlgebraicClosure]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k)))]

attribute [local instance] DerivedCategory.braidedCategory'

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  [HasCompactification f.geometricFiberToAlgebraicClosure] [Finite Λ]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k)))] in
/-- **The local terms of the constant sheaf**: at a point `x̄` of `X₀(𝔽_{q^m})`, the local
Frobenius `F_{x̄,m}` of the canonical Weil structure of `Λ_X` is the identity of the stalk
`(Λ_X)_x̄ = Λ`; its trace is `1`. -/
theorem trace_localOperator_unit {m : ℕ} (x : geometricFixedPoint f m)
    [HasRightDual ((geometricStalk Λ x.1).obj (𝟙_ _))] :
    trace (localOperator Λ x.2.2 (iterateWeilDatum Λ _
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f.geometricGaloisFrobenius.asIso.hom).hom
        m)) =
      𝟙 _ := by
  rw [iterateWeilDatum_leftDerivedUpperStarUnitIso]
  exact trace_localOperator_leftDerivedUpperStarUnitIso Λ x.2.2

/-- For the constant sheaf `Λ_X` with its canonical Weil structure and every `m ≥ 1`, the trace of
`Frob_{X,Λ_X}^m` on `RΓ_c(X, Λ_X)` is `#X₀(𝔽_{q^m}) · 1_Λ`. -/
theorem trace_globalOperator_unit_eq_natCard {m : ℕ} (hm : m ≠ 0)
    [HasRightDual ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ)
      f.geometricFiberToAlgebraicClosure).obj (𝟙_ _))]
    [∀ x : geometricFixedPoint f m, HasRightDual ((geometricStalk Λ x.1).obj (𝟙_ _))] :
    trace (globalOperator Λ (isPullback_endIterate f.isPullback_geometricGaloisFrobenius m)
      (iterateWeilDatum Λ _
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f.geometricGaloisFrobenius.asIso.hom).hom
          m)) =
      (Nat.card (geometricFixedPoint f m) :
        End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} Λ)))).asHom := by
  have := finite_geometricFixedPoint f hm
  have := Fintype.ofFinite (geometricFixedPoint f m)
  rw [trace_globalOperator_iterateWeilDatum_eq_finsum f Λ (constructibleFiniteTor_unit Λ) _ hm,
    finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl fun x _ ↦ trace_localOperator_unit f Λ x, Finset.sum_const,
    Finset.card_univ, Nat.card_eq_fintype_card,
    ← nsmul_one (A := End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} Λ))))]
  exact (map_nsmul End.addEquiv _ 1).symm

end AlgebraicGeometry.Etale
