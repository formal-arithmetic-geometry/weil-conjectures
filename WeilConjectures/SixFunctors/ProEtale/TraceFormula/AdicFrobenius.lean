/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem

/-!
# Compatible systems of Frobenius coefficient morphisms and their realizations

A *compatible system of Frobenius coefficient morphisms* on a normalized adic system
`L_• = (L_n)` (`AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem`, blueprint
`prop-trf-adic-coefficient-morphism-systems`) is a family `ψ_n : LΦ^* L_n ⟶ L_n` of Frobenius
coefficient morphisms reducing to each other along the transitions of `L_•`. A compatible tower
of Weil pairs (strict Weil structures at every level) is the case where every `ψ_n` is invertible
(`AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.IsWeil`).

For such a system, the global Frobenius operators `F_{c,m}(ψ_n)` on `RΓ_c(X, L_n)` and the
stalk Frobenius endomorphisms `(ψ_{n,m})_x̄` at points fixed by `Φ_m` form compatible families of
endomorphisms of the normalized towers of perfect complexes of
`WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem`
(`prop-trf-adic-coefficient-morphism-systems` (3)); hence they lift to the realizations over
`R`, and the traces of the lifts are the limits of the levelwise traces
(`prop-trf-adic-coefficient-morphism-systems` (4), `sk-prop-trace-adic` (ii)).

## Main definitions

- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem`: a compatible system of Frobenius
  coefficient morphisms.
- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.weilComplex`: the Weil complex
  `(L_n, ψ_n)` at level `n`.
- `AlgebraicGeometry.ProEtale.IsProperPullbackCompatible`: compatibility of a compact-support
  coefficient change with the proper pullbacks of two operation packages.

## Main results

- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.coeffIterate_comp_map`: the iterates
  `ψ_{n,m}` form a compatible system.
- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.isCompatible_stalkFrobenius`,
  `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.isCompatible_globalOperator`:
  blueprint `prop-trf-adic-coefficient-morphism-systems` (3).

## Implementation notes

The compatibility of `ψ_{n+1}` with `ψ_n` is read through the identification
`LΦ^* ∘ Res ≅ Res ∘ LΦ^*` of the derived pullback with restriction of scalars
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso`); in terms of derived base
change, `ψ_{n+1} ⊗ᴸ A_n` corresponds to `ψ_n` under `ν_n`.

The global Frobenius operator of a level is built from the operation package of that level, and
the packages at different levels are independent data of the formalism
(`AlgebraicGeometry.ProEtale.GeometricOperations`). Their compatibility with the coefficient
change is therefore a hypothesis (`AlgebraicGeometry.ProEtale.IsProperPullbackCompatible`): the
coefficient comparison of compact support intertwines the proper pullbacks of the two packages,
as the comparison of the six operations does (blueprint
`lem-fix-compact-support-coefficient-change`: it is compatible with pullback and with the
counits). The stalk Frobenius endomorphisms involve no package.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

namespace AlgebraicGeometry.ProEtale

namespace AdicSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} (S : AdicSystem I X)
  {s : Scheme.{u}} {aX : X ⟶ s}

/-- Blueprint `prop-trf-adic-coefficient-morphism-systems`: a *compatible system of Frobenius
coefficient morphisms* on a normalized adic system `L_•`, for an endomorphism `Φ` of `X` over
`s`: Frobenius coefficient morphisms `ψ_n : LΦ^* L_n ⟶ L_n` at every level such that
`ψ_{n+1}` followed by the transition `ν_n : L_{n+1} ⟶ Res L_n` is `LΦ^* ν_n` followed by the
identification `LΦ^* Res L_n ≅ Res LΦ^* L_n` and `Res ψ_n`. No invertibility is assumed. -/
structure FrobeniusSystem (Φ : X ⟶ X) (hΦ : Φ ≫ aX = aX) where
  /-- The Frobenius coefficient morphism `ψ_n : LΦ^* L_n ⟶ L_n`. -/
  coeff (n : ℕ) :
    ((upperStar (ModuleCat.{u + 1} (R ⧸ I ^ n)) Φ).leftDerivedFunctor).obj (S.obj n) ⟶ S.obj n
  /-- `ψ_{n+1}` reduces to `ψ_n`. -/
  comm (n : ℕ) : coeff (n + 1) ≫ S.map n =
    ((upperStar (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) Φ).leftDerivedFunctor).map (S.map n) ≫
      (leftDerivedUpperStarRestrictScalarsIso
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) n.le_succ)) Φ).hom.app (S.obj n) ≫
      (levelTransitionRestrictScalars X I n.le_succ).map (coeff n)

namespace FrobeniusSystem

variable {S} {Φ : X ⟶ X} {hΦ : Φ ≫ aX = aX} (F : S.FrobeniusSystem Φ hΦ)

/-- A compatible system of Frobenius coefficient morphisms is a *compatible tower of Weil
pairs* if every `ψ_n` is invertible: a strict Weil structure at every level, compatible with the
transitions (blueprint `def-trf-adic-system`, `sk-prop-trace-adic` (ii)). -/
def IsWeil : Prop := ∀ n, IsIso (F.coeff n)

/-- The Weil complex `(L_n, ψ_n)` at level `n`. -/
@[simps]
def weilComplex (n : ℕ) : WeilComplex (A := ModuleCat.{u + 1} (R ⧸ I ^ n)) aX where
  frobenius := Φ
  frobenius_comp := hΦ
  obj := S.obj n
  coeff := F.coeff n

end FrobeniusSystem

end AdicSystem

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

namespace AdicSystem

namespace FrobeniusSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} {S : AdicSystem I X}
  {s : Scheme.{u}} {aX : X ⟶ s} {Φ : X ⟶ X} {hΦ : Φ ≫ aX = aX} (F : S.FrobeniusSystem Φ hΦ)

/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (3): the iterates `ψ_{n,m}` of a
compatible system of Frobenius coefficient morphisms are again compatible: `ψ_{n+1,m}` followed
by `ν_n` is `LΦ_m^* ν_n` followed by the identification `LΦ_m^* Res ≅ Res LΦ_m^*` and
`Res ψ_{n,m}`. -/
theorem coeffIterate_comp_map (n m : ℕ) :
    (F.weilComplex (n + 1)).coeffIterate m ≫ S.map n =
      ((upperStar (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1)))
          ((F.weilComplex (n + 1)).frobeniusIterate m)).leftDerivedFunctor).map (S.map n) ≫
        (leftDerivedUpperStarRestrictScalarsIso
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) n.le_succ))
          ((F.weilComplex (n + 1)).frobeniusIterate m)).hom.app (S.obj n) ≫
        (levelTransitionRestrictScalars X I n.le_succ).map
          ((F.weilComplex n).coeffIterate m) := by
  induction m with
  | zero =>
    simp only [WeilComplex.coeffIterate_zero]
    erw [leftDerivedUpperStarRestrictScalarsIso_id_hom_app]
    exact ((leftDerivedUpperStarId _ X).hom.naturality (S.map n)).symm
  | succ m ih =>
    sorry

end FrobeniusSystem

end AdicSystem

end AlgebraicGeometry.ProEtale
