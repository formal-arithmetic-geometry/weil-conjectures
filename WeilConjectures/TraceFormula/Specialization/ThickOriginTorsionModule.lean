/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ThickOriginFiniteModule

/-!

# The thick origin for every finite module over a finite `ℓ`-torsion ring

Let `X = 𝔸¹_k` and `Z = V(x^m)` with `m ≥ 1`, and let `T` be a finite commutative ring killed by a
power of a prime `ℓ ≠ char k'`. Blueprint `lemma-case-z-v-x-m--1` asserts that the defect
`C_{X,Z}(M_X)` of the constant complex of every finite `T`-module `M` vanishes
(`ProEtale.CondensedRing.isZero_specializationDefect_polyAffineThickOrigin_finiteModule`).

The library proves this for finite free modules over a ring killed by `ℓ` (`ProEtale.CondensedRing.
isZero_specializationDefect_polyAffineThickOrigin_finiteCoefficientConstant`).
The general case is stated here; its proof (the homotopy argument of the blueprint, along the
contraction `𝔸¹ × 𝔸¹ ⟶ 𝔸¹, (x, a) ↦ a x`) is not formalised yet.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **The case `Z = V(x^m) ⊆ 𝔸¹`** (blueprint `lemma-case-z-v-x-m--1`): let `T` be a finite
commutative ring killed by a power `ℓ^n` of a prime `ℓ ≠ char k'`. For `X = 𝔸¹_k`,
`Z = V(x^m)` with `m ≥ 1` and every finite `T`-module `M`, the defect `C_{X,Z}(M_X)` of the
constant complex `M_X` vanishes. -/
theorem isZero_specializationDefect_polyAffineThickOrigin_finiteModule {n : ℕ}
    (hT : (ℓ : T) ^ n = 0) {m : ℕ} (hm : 0 < m) (M : ModuleCat.{u + 1} (ULift.{u + 1} T))
    [Module.Finite (ULift.{u + 1} T) M] :
    IsZero (specializationDefect (polyAffine k 1) (polyAffineThickOrigin k m) k'
      (Profinite.continuousMapRingObj.{u} T)
      ((finiteCoefficientConstantFunctor T (polyAffine k 1).left).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
