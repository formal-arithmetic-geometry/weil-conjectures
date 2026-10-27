/-
Copyright (c) 2026 Q130. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q130
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Tensor

/-!
# Length-one flat resolutions and valuation local rings

Source: Stacks Project, More on Algebra, Tags 092S and 092D,
`lemma-weak-dimension-at-most-1` and `definition-weak-dimension`
(blueprint: lem-trf-weak-dimension-one-valuation-criterion).

The first statement gives the criterion for arbitrary commutative rings, including the zero
ring; the second gives its nonzero local specialization. The domain structures are conclusions,
not hypotheses. Modules have arbitrary size `max u v`, containing the ring universe.
-/

@[expose] public section

universe u v

set_option autoImplicit false

namespace Ring

/-- Every module has a flat resolution of length at most one if and only if every prime
localization is a valuation domain. Source: Stacks Project, Tag 092S, equivalence (1) and (5),
and Tag 092D (blueprint: lem-trf-weak-dimension-one-valuation-criterion).

Proof:
1. Apply a length-one flat resolution to `R/I`. Choose a lift `x` of `1` in its flat module
`F₀`. The pullback `E = {(u,r) | b(u) = r mod I}` is isomorphic to `F₁ ⊕ R`, via
`(v,r) ↦ (a(v) + r • x,r)`, so is flat by the tensor-injectivity definition
(def-weil-pbc-flat-ring-map).
2. The projection `E → F₀` is surjective with kernel `I`. The flat-kernel theorem
(lem-weil-pbc-flat-ses-kernel-flat) makes every ideal of `R` flat.
3. For a prime `p`, every ideal of `Rₚ` is the localization of its inverse image in `R`
(lem-trf-module-submodule-localization). Base change preserves flatness
(lem-weil-pbc-flat-module-base-change), so every ideal of `Rₚ` is flat. The localization
is nonzero and local (def-weil-pbc-localization-at-prime).
4. Every finitely generated ideal of this local ring is free
(lem-weil-pbc-finite-flat-local-free). A nonzero free ideal has rank one: two different
basis elements `x,y` would give the nontrivial relation `y • x - x • y = 0`.
Its generator is a nonzerodivisor. Applying this to each nonzero principal ideal shows
that every nonzero element is a nonzerodivisor, so the ring is a domain.
5. Write `(f,g) = (h)` with `f = a*h`, `g = b*h`, `h = c*f+d*g`. Cancellation gives
`c*a+d*b = 1`; locality makes `a` or `b` a unit. Thus either `f` divides `g` or `g`
divides `f`, which is the valuation-ring criterion (def-trf-valuation-ring).
6. Conversely, every localized ideal at a maximal ideal embeds in the corresponding
valuation domain by exactness of localization (lem-weil-pbc-localization-module-exact).
It is torsion-free, hence flat (lem-trf-valuation-torsionfree-flat). Restrict scalars
(lem-weil-pbc-flat-over-localization), then descend flatness from maximal localizations
(lem-sfb-base-flatness-maximal-localizations). This proves that every ideal is flat,
including for the zero ring, where there are no maximal ideals.
7. If `N ⊆ P` and `P` is flat, a finitely generated ideal `J` is flat by step 6.
Thus `J ⊗ N → J ⊗ P → P` is injective. This composite factors as the multiplication
map `J ⊗ N → N` followed by inclusion. The finitely generated ideal criterion
(lem-weil-pbc-flat-fg-ideal-criterion) therefore makes `N` flat.
8. Take the free surjection `R^(M) → M`. Its source is flat
(lem-weil-pbc-projective-module-flat), and step 7 makes its kernel flat, giving the
required resolution without any finite-generation assumption.
9. For a nonzero local ring, steps 1--5 apply directly to the ring itself. Conversely,
over a valuation domain every ideal is torsion-free, hence flat, so steps 7--8 apply.
This also gives the local consequence stated below. -/
theorem flat_resolution_length_one_iff_prime_localizations_valuation
    (R : Type u) [CommRing R] :
    (∀ M : ModuleCat.{max u v} R,
      ∃ F₀ F₁ : ModuleCat.{max u v} R,
        Module.Flat R F₀ ∧ Module.Flat R F₁ ∧
          ∃ (a : F₁ →ₗ[R] F₀) (b : F₀ →ₗ[R] M),
            Function.Injective a ∧ Function.Surjective b ∧ LinearMap.range a = LinearMap.ker b) ↔
      ∀ (p : Ideal R) [p.IsPrime],
        ∃ h : IsDomain (Localization.AtPrime p), @ValuationRing (Localization.AtPrime p) _ h := by
  sorry

/-- The local consequence of the length-one flat-resolution criterion: a nonzero local
commutative ring has such resolutions for every module if and only if it is a valuation domain.
Source: Stacks Project, Tag 092S, proof of (1) implies (5), and Tag 0539
(blueprint: lem-trf-weak-dimension-one-valuation-criterion).

Proof: Apply a resolution to each `R/I` and use the pullback comparison and the flat-kernel
lemma (lem-weil-pbc-flat-ses-kernel-flat) to make every ideal flat. Finite flat modules over
local rings are free (lem-weil-pbc-finite-flat-local-free). A nonzero free ideal has rank
one by commutativity; its generator is a nonzerodivisor. Thus the ring is a domain and
its finitely generated ideals are principal. For `(f,g) = (h)`, locality and cancellation
make `f/h` or `g/h` a unit, proving the valuation criterion (def-trf-valuation-ring).
Conversely, ideals of a valuation domain are torsion-free and hence flat
(lem-trf-valuation-torsionfree-flat). The injectivity square for `J ⊗ N → J ⊗ P`
and the finitely generated ideal criterion (lem-weil-pbc-flat-fg-ideal-criterion) make
submodules of flat modules flat. A free surjection onto any module is flat
(lem-weil-pbc-projective-module-flat), and its flat kernel gives the required resolution. -/
theorem flat_resolution_length_one_iff_valuation_of_isLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (∀ M : ModuleCat.{max u v} R,
      ∃ F₀ F₁ : ModuleCat.{max u v} R,
        Module.Flat R F₀ ∧ Module.Flat R F₁ ∧
          ∃ (a : F₁ →ₗ[R] F₀) (b : F₀ →ₗ[R] M),
            Function.Injective a ∧ Function.Surjective b ∧ LinearMap.range a = LinearMap.ker b) ↔
      ∃ h : IsDomain R, @ValuationRing R _ h := by
  sorry

end Ring
