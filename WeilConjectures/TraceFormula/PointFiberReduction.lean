/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegral

/-!

# The integral point fibre functor modulo `ℓⁿ`

Over the separably closed point `s = Spec k`, the integral point fibre functor
`Fib_s : Dᵇc(s)⟦𝒪̲_E⟧ ⥤ D(𝒪_E)` (`ProEtale.CondensedRing.pointFiberFunctorIntegral`) and the
reduction modulo `ℓⁿ` read on the étale site (`ProEtale.CondensedRing.etaleReduction`) are
related by the reduction triangle: for every `N`, there is a distinguished triangle
```
Fib_s(N) --ℓⁿ--> Fib_s(N) --π--> RΓ(s, N ⊗ᴸ 𝒪_E ⧸ ℓⁿ) ⟶ Fib_s(N)[1]
```
in `D(𝒪_E)`, the last object read through restriction of scalars along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`,
with `π` natural in `N` (`ProEtale.CondensedRing.exists_pointFiberFunctorIntegral_reduction`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : FiniteIntermediateField ℓ) (n : ℕ)

/-- The reduction `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, between the universe-lifted coefficient rings of the
integral point fibre functor and of the étale reduction. -/
noncomputable def integersModPowCoeffHom :
    Shrink.{u + 1} (integers ℓ E.1) →+* integersModPowCoeff.{u} ℓ E.1 n :=
  (ULift.ringEquiv.symm.toRingHom).comp
    ((integersModPowMk ℓ E.1 n).comp (Shrink.ringEquiv _).toRingHom)

/-- **The integral point fibre functor modulo `ℓⁿ`**: there is a natural transformation
`π : Fib_s ⟶ RΓ(s, (-) ⊗ᴸ 𝒪_E ⧸ ℓⁿ)` (read in `D(𝒪_E)`) such that for every `N` the triangle
`Fib_s(N) --ℓⁿ--> Fib_s(N) --π--> RΓ(s, N ⊗ᴸ 𝒪_E ⧸ ℓⁿ) ⟶` is distinguished. -/
theorem exists_pointFiberFunctorIntegral_reduction :
    ∃ π : pointFiberFunctorIntegral ℓ k E ⟶
        etaleReduction ℓ E.1 n (point k) ⋙
          Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
            (point k).left ⋙
          (ModuleCat.restrictScalars (integersModPowCoeffHom.{u} ℓ E n)).mapDerivedCategory,
      ∀ N, ∃ δ, Pretriangulated.Triangle.mk
        (((ℓ : ℤ) ^ n) • 𝟙 ((pointFiberFunctorIntegral ℓ k E).obj N))
        (π.app N) δ ∈ distTriang _ :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
