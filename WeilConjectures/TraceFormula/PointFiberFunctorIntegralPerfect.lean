/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegral

/-!

# Integral point fibres are perfect

Over the separably closed point `s = Spec k`, the integral point fibre functor
`Fib_s : Dᵇc(s)⟦𝒪̲_E⟧ ⥤ D(𝒪_E)` (`ProEtale.CondensedRing.pointFiberFunctorIntegral`) takes values
in perfect complexes: the cohomology of `Fib_s(N)` is bounded and finitely generated over the
discrete valuation ring `𝒪_E`, hence `Fib_s(N)` is perfect
(`ProEtale.CondensedRing.isPerfect_pointFiberFunctorIntegral_obj`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : FiniteIntermediateField ℓ)

/-- **Integral point fibres are perfect**: for a bounded constructible `𝒪_E`-complex `N` over the
separably closed point, `Fib_s(N)` is a perfect complex of `𝒪_E`-modules. -/
theorem isPerfect_pointFiberFunctorIntegral_obj
    (N : Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    ((pointFiberFunctorIntegral ℓ k E).obj N).IsPerfect :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
