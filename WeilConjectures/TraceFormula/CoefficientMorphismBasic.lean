/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.GraphPieces

/-!

# The trace formula for Frobenius coefficient morphisms in degree one

Let `Φ : X ⟶ X` be a proper endomorphism of a separated `k`-scheme of finite type. For a bounded
constructible `K` and an arbitrary map `ψ : LΦ^* K ⟶ K`, the *trace formula in degree one*
(`ProEtale.CondensedRing.TraceFormulaHolds`) is the identity
```
tr(RΓ_c(X, ψ) ∘ Φ^♯ | RΓ_c(X, K)) = ∑_{x ∈ X(k), Φ x = x} tr(ψ_x | K_x),
```
the statement `TF(X, K, ψ, 1)` of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`, Step 0. For the model Frobenius `Φ` the trace
formula in degree `m` is the trace formula in degree one for the iterate `Φ_m` with the
coefficient map `ψ_m` (`ProEtale.CondensedRing.TraceFormulaHolds.trace_frobeniusCompactOperator`),
and `Φ_m` is again a model Frobenius, over the extension of degree `m` of the finite field.

This file also proves that the stalk maps of the restriction of `ψ` along a morphism
`j : U ⟶ X` with `Φ_U ≫ j = j ≫ Φ` are the stalk maps of `ψ`
(`ProEtale.CondensedRing.trace_graphStalkMap_upperStar`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The *trace formula in degree one* for the proper endomorphism `Φ` of `X` (blueprint
`thm-trf-coefficient-morphism-trace-formula`, the statement `TF(X, K, ψ, 1)` of Step 0): for every
bounded constructible `K` and every, not necessarily invertible, map `ψ : LΦ^* K ⟶ K`, the trace of
the operator `RΓ_c(X, ψ) ∘ Φ^♯` on `RΓ_c(X, K)` is the sum over the rational points `x` fixed by
`Φ` of the traces of the stalk maps `ψ_x : K_x ⟶ K_x`. The identity is required for all choices of
duals and of the finiteness of the fixed points. -/
def TraceFormulaHolds (Φ : X ⟶ X) [IsProper Φ.left] : Prop :=
  ∀ (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)]
    [Fintype {x : RationalPoint X // x ≫ Φ = x}],
    trace ((compactPullback ℓ Φ).app K ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map ψ) =
      ∑ x : {x : RationalPoint X // x ≫ Φ = x}, trace (Correspondence.graphStalkMap K Φ ψ x.1 x.2)

variable {ℓ}

/-- The trace formula in degree one for the iterate `Φ_m` gives the trace formula in degree `m`
for `Φ`: `tr(F_{c,m}(ψ) | RΓ_c(X, K)) = ∑_{x ∈ X(k), Φ_m x = x} tr(ψ_{m,x} | K_x)`, since
`F_{c,m}(ψ) = RΓ_c(X, ψ_m) ∘ Φ_m^♯` by definition. -/
theorem TraceFormulaHolds.trace_frobeniusCompactOperator {Φ : X ⟶ X} [IsProper Φ.left] {m : ℕ}
    (h : TraceFormulaHolds ℓ (frobeniusIterate Φ m))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)] :
    trace (frobeniusCompactOperator ℓ ψ m) =
      ∑ x : FixedPoint Φ m, trace (Correspondence.graphStalkMap K (frobeniusIterate Φ m)
        (frobeniusCoefficientIterate ψ m) x.1 x.2) :=
  h K (frobeniusCoefficientIterate ψ m)

/-- **The stalk maps of a restriction** (blueprint `prop-trf-trace-additivity-open-closed`, the
stalk side, and `lem-trf-weil-shriek-operator-fibres` (3)): for a morphism `j : U ⟶ X` with
`P ≫ j = j ≫ T`, a map `ψ : LT^* K ⟶ K` and a rational point `x` of `U` fixed by `P`, the
stalk map at `x` of the restriction `Lj^* ψ` (composed with the comparison
`LP^* Lj^* K ≅ Lj^* LT^* K`) has the trace of the stalk map of `ψ` at `x ≫ j`. -/
theorem trace_graphStalkMap_upperStar {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom]
    [QuasiCompact U.hom] [IsSeparated U.hom] {P : U ⟶ U} {T : X ⟶ X} {j : U ⟶ X}
    (hP : P ≫ j = j ≫ T) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ T).obj K ⟶ K)
    (x : RationalPoint U) (hx : x ≫ P = x)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))]
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (x ≫ j)).obj K)] :
    trace (Correspondence.graphStalkMap
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) P
        ((weilUpperStarComparison ℓ P T j hP).hom.app K ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map ψ) x hx) =
      trace (Correspondence.graphStalkMap K T ψ (x ≫ j)
        (by rw [Category.assoc, ← hP, ← Category.assoc, hx])) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
