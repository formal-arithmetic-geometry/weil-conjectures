/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Rigid.BraidedTrace
public import WeilConjectures.TraceFormula.GrothendieckLefschetz.Integral
public import WeilConjectures.ZetaFunction.PerfectComplexLogDeterminant

/-!
# The Grothendieck–Lefschetz trace formula with coefficients in a finite extension of `ℚ_ℓ`

Let `E` be a finite extension of `ℚ_ℓ` with ring of integers `R = 𝒪_E`. An object `K_E` of
`Dᵇc(X, E)` with a Weil structure `ψ_E` has an integral model: a normalized system `L_•` over
`𝒪_E` with a compatible system `θ_•` of (not necessarily invertible) Frobenius correspondences
and an integer `N ≥ 0` with `ψ_E = π_E^{-N} (θ ⊗ E)` (blueprint
`lemma-integral-models-rational-frobenius-correspondences`). Its compact cohomology and its
stalks are the scalar extensions `G(P) = P ⊗ᴸ_{𝒪_E} E` of the integral realizations `P`, and the
Frobenius operators of `ψ_E` are `π_E^{-Nm} G(V)` for the lifts `V` of the integral operators
of `θ` (blueprint `lemma-integral-models-rational-frobenius-correspondences--2`). This file
proves the trace formula for them (blueprint
`theorem-grothendieck-lefschetz-trace-formula--3`): by linearity of the categorical trace over
the field `E` (`DerivedCategory.IsPerfect.trace_smul`), its compatibility with the braided
monoidal scalar extension `G` (`CategoryTheory.Functor.trace_eq_unitEndRingHom_trace`) and the
integral trace formula
`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.trace_eq_finsum_trace`.

The scalar extension `G` is any additive braided monoidal functor `D(𝒪_E) ⥤ D(E)`, and the
scalar `π_E^{-Nm}` is any `t ∈ E`. No `E`-coefficient sheaf appears in the statement: this is the
reduction step of clause `--3`, the integral formula transported along `G` and scaled by `t`. The
identification of `RΓ_c(X, K_E)`, of the stalks `(K_E)_x̄` and of their Frobenius operators with
`G(P_R)`, `G(P_{x̄,R})` and `t • G(V)`, `t • G(V_x̄)` (clause `--2` of
`lemma-integral-models-rational-frobenius-correspondences`) is not part of this file.
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
  {E : Type (u + 1)} [Field E]

/-- **The Grothendieck–Lefschetz trace formula with coefficients in a finite extension `E` of
`ℚ_ℓ`** (blueprint `theorem-grothendieck-lefschetz-trace-formula--3`): with the notation of
`trace_eq_finsum_trace`, for `R = 𝒪_E`, the derived scalar extension `G : D(𝒪_E) ⥤ D(E)` and
`t = π_E^{-Nm}`, the global Frobenius operator `t • G(V)` on `RΓ_c(X, K_E) = G(P_R)` and the
local Frobenius operators `t • G(V_x̄)` on the stalks `(K_E)_x̄ = G(P_{x̄,R})` satisfy
```
tr_E(Frob_{X,K_E}^m ∣ RΓ_c(X, K_E)) = ∑_{x̄ ∈ X₀(𝔽_{q^m})} tr_E(Frob_{x̄,m} ∣ (K_E)_x̄).
```
This is the reduction step only: the statement is about `t • G(V)` and `t • G(V_x̄)` for an
arbitrary braided functor `G` and scalar `t`, and does not mention an `E`-coefficient sheaf; the
identification of the Frobenius operators of `K_E` with them is left to the caller.
-/
theorem trace_smul_map_eq_finsum_trace (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R)
    (hI : I = Ideal.span {ϖ})
    (F : S.FrobeniusSystem f.geometricGaloisFrobenius.hom) {m : ℕ} (hm : m ≠ 0)
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
      ((F.iterate m).localOperatorFamily x.2.2 (β x) (hβ x)) (Vx x))
    (G : DerivedCategory (ModuleCat.{u + 1} R) ⥤ DerivedCategory (ModuleCat.{u + 1} E))
    [G.Braided] [G.Additive] (hG : (G.obj c.pt).IsPerfect)
    (hGx : ∀ x : geometricFixedPoint f m, (G.obj (cx x).pt).IsPerfect)
    [HasRightDual (G.obj c.pt)] [∀ x : geometricFixedPoint f m, HasRightDual (G.obj (cx x).pt)]
    (t : E) :
    trace (t • G.map V) = ∑ᶠ x : geometricFixedPoint f m, trace (t • G.map (Vx x)) := by
  have := finite_geometricFixedPoint f hm
  have := Fintype.ofFinite (geometricFixedPoint f m)
  have h := trace_eq_finsum_trace f hϖ hI F hm α hα hα' hc hV β hβ hβ' cx hcx Vx hVx
  rw [hG.trace_smul, G.trace_eq_unitEndRingHom_trace V _ (Iso.refl _) (by simp), h,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [(hGx x).trace_smul, G.trace_eq_unitEndRingHom_trace (Vx x) _ (Iso.refl _) (by simp)]

end AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem
