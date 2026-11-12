/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.CategoricalTrace
public import WeilConjectures.TraceFormula.GrothendieckLefschetz.Finite

/-!
# The Grothendieck–Lefschetz trace formula with integral coefficients

Let `R` be a complete local ring with ideal `I = (ϖ)`, `ϖ` in the maximal ideal, such that the
quotients `A_n = R ⧸ Iⁿ` are finite with exponent invertible in `k̄` (for instance `R = 𝒪_E`,
`ϖ = π_E`). An object of `Dᵇc(X, R)` on the geometric fibre `X = X₀ ×_k k̄` of a separated scheme
of finite type over `k = 𝔽_q` is a normalized system `L_•` (`AlgebraicGeometry.Etale.AdicSystem`)
of objects `L_n ∈ Dᵇctf(X, A_n)`, and a Weil structure is a compatible system `ψ_•` of Weil data
(`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem`). Its compact cohomology and its stalks are
the realizations `R lim_n RΓ_c(X, L_n)` and `R lim_n (L_n)_x̄`, which are perfect complexes over
`R`, and the Frobenius operators on them are the lifts of the levelwise operators
(`AlgebraicGeometry.Etale.adicRealization`).

This file proves the trace formula for them,
```
tr_R(F_{c,m} ∣ RΓ_c(X, L)) = ∑_{x̄ ∈ X₀(𝔽_{q^m})} tr_R(F_{x̄,m} ∣ L_x̄),
```
(blueprint `theorem-grothendieck-lefschetz-trace-formula--2`), from the formula at the finite
levels `AlgebraicGeometry.Etale.trace_globalOperator_iterateWeilDatum_eq_finsum`: by
`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.exists_trace_eq_globalOperatorFamily`, both
sides reduce modulo `Iⁿ⁺¹` to the two sides of the formula at the level `n + 1`, and `R` is
`I`-adically separated. As at the finite levels, the Weil data need not be invertible.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem

open Scheme

attribute [local instance] DerivedCategory.braidedCategory'

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  [HasCompactification f.geometricFiberToAlgebraicClosure]
  {R : Type (u + 1)} [CommRing R] [IsLocalRing R] {I : Ideal R} [IsAdicComplete I R] {ϖ : R}
  [∀ n, Finite (R ⧸ I ^ n)]
  [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of (AlgebraicClosure k)))]
  {S : AdicSystem I f.geometricFiber}

/-- **The Grothendieck–Lefschetz trace formula with integral coefficients** (blueprint
`theorem-grothendieck-lefschetz-trace-formula--2`): for a compatible system `ψ_•` of Weil data
on a normalized system `L_•` over `R` (for instance `R = 𝒪_E`), and every `m ≥ 1`, the trace of
the lift `V` of the global Frobenius operators `F_{c,m}(ψ_n)` to the realization
`P_R = R lim_n RΓ_c(X, L_n)` is the sum, over the points `x̄` of `X₀(𝔽_{q^m})`, of the traces
of the lifts `V_x̄` of the local Frobenius operators `F_{x̄,m}(ψ_n)` to the realizations
`R lim_n (L_n)_x̄`:
```
tr_R(F_{c,m} ∣ RΓ_c(X, L)) = ∑_{x̄} tr_R(F_{x̄,m} ∣ L_x̄).
```
The coefficient identifications `α`, `β` are those of the realizations
(`AlgebraicGeometry.Etale.adicRealization`), compatible with the Frobenius pullbacks. -/
theorem trace_eq_finsum_trace (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R) (hI : I = Ideal.span {ϖ})
    (F : S.FrobeniusSystem f.geometricGaloisFrobenius.hom) {m : ℕ} (hm : m ≠ 0)
    [Finite (geometricFixedPoint f m)]
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars f.geometricFiber.smallEtaleTopology
        (I.powSuccFactor n) ⋙ compactlySupportedGlobalSections (ModuleCat.{u + 1}
          (R ⧸ I ^ (n + 1 + 1))) f.geometricFiberToAlgebraicClosure ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1)))
          f.geometricFiberToAlgebraicClosure ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hα : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n))
    (hα' : ∀ n : ℕ, IsCompactPullbackCompatible (I.powSuccFactor n) (α n)
      (isPullback_endIterate f.isPullback_geometricGaloisFrobenius m))
    {c : Cone (S.compactSupportTower f.geometricFiberToAlgebraicClosure α hα).restrict}
    (hc : IsHomotopyLimit c) [HasRightDual c.pt]
    [∀ n, HasRightDual ((S.compactSupportTower f.geometricFiberToAlgebraicClosure α hα).obj n)]
    {V : c.pt ⟶ c.pt}
    (hV : (S.compactSupportTower f.geometricFiberToAlgebraicClosure α hα).IsLift c
      ((F.iterate m).globalOperatorFamily
        (isPullback_endIterate f.isPullback_geometricGaloisFrobenius m) α hα) V)
    (β : ∀ (x : geometricFixedPoint f m) (n : ℕ),
      Sheaf.derivedRestrictScalars f.geometricFiber.smallEtaleTopology (I.powSuccFactor n) ⋙
          geometricStalk (R ⧸ I ^ (n + 1 + 1)) x.1 ≅
        geometricStalk (R ⧸ I ^ (n + 1)) x.1 ⋙
          ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hβ : ∀ (x : geometricFixedPoint f m) (n : ℕ),
      IsCoefficientChange (I.powSuccFactor n) _ _ (β x n))
    (hβ' : ∀ (x : geometricFixedPoint f m) (n : ℕ),
      IsStalkPullbackCompatible (I.powSuccFactor n) (β x n) x.2.2)
    (cx : ∀ x : geometricFixedPoint f m, Cone (S.stalkTower x.1 (β x) (hβ x)).restrict)
    (hcx : ∀ x : geometricFixedPoint f m, IsHomotopyLimit (cx x))
    [∀ x : geometricFixedPoint f m, HasRightDual (cx x).pt]
    [∀ (x : geometricFixedPoint f m) (n : ℕ),
      HasRightDual ((S.stalkTower x.1 (β x) (hβ x)).obj n)]
    (Vx : ∀ x : geometricFixedPoint f m, (cx x).pt ⟶ (cx x).pt)
    (hVx : ∀ x : geometricFixedPoint f m, (S.stalkTower x.1 (β x) (hβ x)).IsLift (cx x)
      ((F.iterate m).localOperatorFamily x.2.2 (β x) (hβ x)) (Vx x)) :
    trace V = ∑ᶠ x : geometricFixedPoint f m, trace (Vx x) := by
  classical
  have := Fintype.ofFinite (geometricFixedPoint f m)
  obtain ⟨r, hr, hrn⟩ := (F.iterate m).exists_trace_eq_globalOperatorFamily hϖ hI _ α hα hα' hc hV
  choose rx hrx hrxn using fun x ↦ (F.iterate m).exists_trace_eq_localOperatorFamily hϖ hI
    x.2.2 (β x) (hβ x) (hβ' x) (hcx x) (hVx x)
  have hlevel (n : ℕ) : I.powSuccMk n r = I.powSuccMk n (∑ x, rx x) := by
    apply DerivedCategory.algebraMap_injective (R ⧸ I ^ (n + 1))
    rw [← hrn n, map_sum, map_sum]
    simp_rw [← hrxn _ n]
    rw [← finsum_eq_sum_of_fintype]
    have h := trace_globalOperator_iterateWeilDatum_eq_finsum f (R ⧸ I ^ (n + 1))
      (S.boundedConstructibleFiniteTor (n + 1)) (F.coeff (n + 1)) hm (_hΓ := inferInstanceAs
        (HasRightDual ((S.compactSupportTower f.geometricFiberToAlgebraicClosure α hα).obj n)))
      (_hx := fun x ↦ inferInstanceAs (HasRightDual ((S.stalkTower x.1 (β x) (hβ x)).obj n)))
    exact h
  have hr' : r = ∑ x, rx x := by
    refine sub_eq_zero.1 (IsHausdorff.haus (inferInstance : IsHausdorff I R) _ fun n ↦ ?_)
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    rcases n with _ | n
    · simp
    · exact Ideal.Quotient.eq.1 (hlevel n)
  rw [hr, hr', map_sum, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun x _ ↦ (hrx x).symm

end AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem
