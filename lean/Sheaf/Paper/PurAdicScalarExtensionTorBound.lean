/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralCtfTriangulated
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import all Sheaf.Paper.AdicCoefficientDatum
import all Sheaf.SecSmoothPurity.ScalarExtensionFunctor

/-!
# Finite coefficient extension preserves the uniform Tor interval

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md,
Unit Step 2: ordinary derived coefficient extension preserves the finite-Tor domain
(blueprint: lem-pur-adic-scalar-extension-tor-bound).
-/

@[expose] public section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard

universe d u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Ordinary completed scalar extension commutes with reduction at the same positive
exponent. This comparison requires neither constructibility nor derived completeness.
The integer inclusion sends the source uniformizer into the target maximal ideal,
so the same exponent is always sufficient, even for ramified extensions.

Source: blueprint scalar-extension tower proof, first paragraph; Stacks Tags 06YY
and 0G7E (blueprint: lem-pur-adic-scalar-extension-tor-bound).

Proof: the defining residue equation of `completedCoefficientMap` identifies the
composites R -> S -> C and R -> A -> C. Resolve an arbitrary R-complex by a K-flat
complex P with flat terms. Change of rings preserves these two properties. Thus
both iterated derived extensions are computed by their termwise scalar extensions.
Associativity sends (c tensor s) tensor p to c*s tensor p, and its inverse inserts
1 in the intermediate scalar factor. Sheafification preserves these mutually inverse
balanced maps. They commute with differentials and augmentations. The universal
left-derived properties descend this natural comparison to the derived categories;
the comparison is invertible because it is invertible on every K-flat resolution. -/
private theorem completedScalarReductionComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u}) (n : ℕ) :
    Nonempty (completedDerivedScalarExtension l E L ι W ⋙
        scalarReductionDerivedExtension l L W n ≅
      scalarReductionDerivedExtension l E W n ⋙
        ProEtale.scalarExtensionFunctor (integralScalarQuotientMap l E L ι n) W) := by
  let φ := completedCoefficientMap l E L ι W
  let ψ := completedIntegralCommRingProjectionUnrestricted l L W n
  let α := completedIntegralCommRingProjectionUnrestricted l E W n
  let β := integralScalarQuotientSheafMap l E L ι W n
  have hs : φ ≫ ψ = α ≫ β :=
    (completedCoefficientMap_existsUnique l E L ι W).exists.choose_spec n
  obtain ⟨f, hf, _⟩ := AlgebraicGeometry.Scheme.derivedReductionComposition
    W φ ψ (α ≫ β) hs
  obtain ⟨g, hg, _⟩ := AlgebraicGeometry.Scheme.derivedReductionComposition
    W α β (α ≫ β) rfl
  have := hf.1
  have := hg.1
  exact ⟨asIso f ≪≫ (asIso g).symm⟩

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
  have _ := he
  have _ := hK
  intro m
  obtain ⟨c⟩ := completedScalarReductionComparison l E L ι W m
  have ht := AlgebraicGeometry.ProEtale.scalarExtension_tor
    (integralScalarQuotientMap l E L ι m) W _ a b (hab m)
  refine ⟨ht.1, ?_⟩
  intro N P hN f hf hP M i hi
  obtain ⟨eN⟩ := hN
  exact ht.2 N P ⟨eN ≪≫ c.app K⟩ f hf hP M i hi

end WeilConjectures
