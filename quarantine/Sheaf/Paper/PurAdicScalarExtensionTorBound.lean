/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralCtfTriangulated
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.SfIntegralConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Finite coefficient extension preserves the uniform Tor interval

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md,
Unit Step 2: ordinary derived coefficient extension preserves the finite-Tor domain
(blueprint: lem-pur-adic-scalar-extension-tor-bound).
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false

universe d u

open CategoryTheory AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Finite coefficient extension preserves the uniform Tor interval: if every reduction of
`K ∈ D^b_ctf(W, 𝒪_E)` has Tor amplitude in `[a,b]`, then every `L`-level reduction of the
ordinary derived change of completed coefficient rings
`C_{L/E,W}(K) = K ⊗^L_{𝒪̂_{E,W}} 𝒪̂_{L,W}` has Tor amplitude in the same `[a,b]`.
The index `m : ℕ` denotes the target level `m + 1`.
Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md,
Unit Step 2: ordinary derived coefficient extension preserves the finite-Tor domain
(blueprint: lem-pur-adic-scalar-extension-tor-bound).
Proof:
1. Write `R = 𝒪̂_{E,W}`, `S = 𝒪̂_{L,W}`, `A = A_{E,n}`, `C = A_{L,m}` with `e * n ≥ m`.
Since `ϖ_E^n 𝒪_L = ϖ_L^{en} 𝒪_L ⊆ ϖ_L^m 𝒪_L`, the map `𝒪_E → C` factors through `A`, and
`R → S → C_W` agrees with `R → A_W → C_W` on limit projections. For a K-flat resolution
`P → K` with flat terms, `P ⊗_R S` represents `C_{L/E,W}(K)`, `Q = P ⊗_R A_W` represents
`K_n`, and by associativity of termwise change of rings the `L`-level reduction is
represented by `P ⊗_R C_W = Q ⊗_A C_W`, a representative of `K_n ⊗^L_A C`; derived change
of rings makes this independent of `P`. Uses: lem-pc-kflat-resolution,
lem-pur-kflat-change-of-rings, lem-pur-derived-change-of-rings,
def-weil-integral-derived-reduction.
2. For a degree-zero `C_W`-module `N`, `(Q ⊗_A C_W) ⊗_C N = Q ⊗_A Res N` termwise and as a
complex, which computes `K_n ⊗^L_A Res N`. By hypothesis `K_n` has Tor amplitude in `[a,b]`,
so its cohomology vanishes outside `[a,b]`; no flatness of `C` over `A` is used.
Uses: def-weil-proetale-tor-amplitude, def-weil-derived-tensor,
lem-pur-kflat-change-of-rings, def-weil-finite-tor-amplitude.
3. The identifications are compatible with transitions in `m`; normalized-DVR effectivity
and the completed scalar comparison identify `C_{L/E,W}(K)` (for derived complete `K`) with
the strict-tower integral scalar extension, which is bounded constructible, so the uniform
interval `[a,b]` holds at every `L`-level. Uses: lem-weil-finite-free-completed-scalar-comparison,
lem-coef-normalized-dvr-effectivity, lem-weil-integral-scalar-extension-constructible,
def-weil-derived-complete-integral-detailed. -/
theorem purAdicScalarExtensionTorBound
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (e : ℕ)
    (he : Ideal.map (integralScalarIntegerInclusion l E L ι)
      (Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E))) =
      Ideal.span ({Padic.coefficientExtensionUniformizer l L} :
        Set (Padic.coefficientExtensionIntegers l L)) ^ e)
    (W : AlgebraicGeometry.Scheme.{u})
    (K : completedIntegralDerivedCategory l E W D hl)
    (hK : integralCtfProperty D l hl E W K)
    (a b : ℤ)
    (hab : ∀ n : ℕ,
      HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l E (n + 1))
        ((integralDerivedReduction l E W D hl n).obj K) a b) :
    ∀ m : ℕ,
      HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l L (m + 1))
        ((integralDerivedReduction l L W D hl m).obj
          ((completedDerivedScalarExtension l E L ι W).obj K)) a b := by
  sorry

end WeilConjectures
