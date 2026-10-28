/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.LocalTermLocality

/-!

# The trace formula for Frobenius coefficient morphisms

Let `Φ` be the model Frobenius of `X = X₀ ×_{k₀} k`, `K` a bounded constructible complex on `X`
and `ψ : LΦ^* K ⟶ K` an arbitrary, not necessarily invertible, morphism (a *Frobenius
coefficient morphism*, blueprint `def-trf-frobenius-coefficient-morphism`), with iterates
`ψ_m : LΦ_m^* K ⟶ K` and global operators `F_{c,m}(ψ) = RΓ_c(X, ψ_m) ∘ Φ_m^♯`
(`ProEtale.CondensedRing.frobeniusCompactOperator`). The trace formula
```
tr(F_{c,m}(ψ) | RΓ_c(X, K)) = ∑_{x ∈ X₀(𝔽_{q^m})} tr(ψ_{m,x} | K_x)
```
(`ProEtale.CondensedRing.trace_frobeniusCompactOperator_eq_sum`, blueprint
`thm-trf-coefficient-morphism-trace-formula`) is the coefficient-morphism variant of the
Grothendieck–Lefschetz formula.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

variable (ℓ) in
/-- **The trace formula for Frobenius coefficient morphisms** (blueprint
`thm-trf-coefficient-morphism-trace-formula`): for the model Frobenius `Φ` of a separated model
`X₀` of finite type over a finite field `k₀`, a bounded constructible `K` with an arbitrary map
`ψ : LΦ^* K ⟶ K` and `m ≥ 1`, the trace of `F_{c,m}(ψ)` on `RΓ_c(X, K)` is the sum over the
rational points `x` fixed by `Φ_m` of the traces of the stalk maps `ψ_{m,x}` on `K_x`. No
invertibility of `ψ` is assumed. -/
theorem trace_frobeniusCompactOperator_eq_sum [IsAlgClosed k] {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p)
    [IsProper Φ.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    {m : ℕ} (hm : 1 ≤ m) [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)] :
    trace (frobeniusCompactOperator ℓ ψ m) =
      ∑ x : FixedPoint Φ m, trace (Correspondence.graphStalkMap K (frobeniusIterate Φ m)
        (frobeniusCoefficientIterate ψ m) x.1 x.2) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
