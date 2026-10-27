module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Nested regular-sequence ideals under finite Tor dimension

Source: Stacks Project, Divided Power Algebra, Tag 09PW (lemma-regular-sequence),
using Tag 09PV (lemma-injective).
(blueprint: lem-sfb-nested-regular-ideals-finite-tor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory.Sequence

/-- If `K ⊆ J` are proper ideals in a Noetherian local ring, `J` is regularly generated,
and `A/J` has finite Tor dimension over `A/K`, then both `K` and `J/K` are regularly
generated. The coefficient module is restricted along the canonical quotient factor map.
The maximal ideal of `A/K` is written as the image of the maximal ideal of `A`.

Source: Stacks Project, Divided Power Algebra, Tag 09PW (lemma-regular-sequence).
(blueprint: lem-sfb-nested-regular-ideals-finite-tor).

Proof:
1. Choose regular generators `y` of `J`. Apply
   lem-trf-lift-regular-generators-through-fibre with both rings `A`, the identity
   map, and both ideals `J`: their residues form a basis of `J/mJ`.
2. The finite Tor hypothesis gives injectivity of `K/mK → J/mJ` by
   lem-sfb-finite-tor-ideal-generators-injective (Stacks Tag 09PV).
3. Noetherianity (def-weil-pbc-noetherian-ring) gives a finite generating list of `K`.
   Reduce it modulo `mK` and retain each vector outside the preceding span. This
   gives a basis with lifts `f₁,…,fₛ` in `K`.
4. Injectivity makes their images independent in `J/mJ`. Extend them to a basis by
   scanning the residues of `y`, lifting the added vectors among the `y`'s.
   Apply lem-sfb-independent-family-spanning-cardinality in both directions to see
   that the extended list has the same length `r` as `y`; hence `s ≤ r`.
5. Nakayama (lem-weil-pbc-nakayama-local-generators) makes the first `s` lifts
   generate `K`. Apply lem-trf-lift-regular-generators-through-fibre again to the
   identity map and ideal `J`: the full lifted basis regularly generates `J`.
6. By lem-weil-pbc-quotient-local-structure, `A/K` is nonzero local with maximal
   ideal `m/K`. The prefix of length `s` is regular by the defining injectivity
   conditions and its nonzero final quotient `A/K`. The remaining images generate
   `J/K`; their successive quotient rings are `A/(f₁,…,fₛ₊ₜ)`, so their successive
   multiplication maps are injective. The final quotient `A/J` is nonzero.
   Thus the tail is regular (def-weil-pbc-regular-sequence). All generators lie
   in `J ⊆ m`, and their images lie in `m/K`. Empty prefixes and tails are allowed;
   if `r = 0` then `J = K = 0`.
-/
theorem exists_regular_generators_nested_of_finite_tor
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K J : Ideal A) (hKJ : K ≤ J) (hJ : J ≤ IsLocalRing.maximalIdeal A)
    (hreg : ∃ ys : List A, Ideal.ofList ys = J ∧ IsRegular A ys)
    (hTor : ∃ d : ℕ, ∀ (N : ModuleCat.{u} (A ⧸ K)) (i : ℕ), d < i →
      IsZero (((Tor' (ModuleCat.{u} (A ⧸ K)) i).obj
        ((ModuleCat.restrictScalars (Ideal.Quotient.factor hKJ)).obj
          (ModuleCat.of (A ⧸ J) (A ⧸ J)))).obj N)) :
    (∃ fs : List A, Ideal.ofList fs = K ∧ IsRegular A fs ∧
      ∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal A) ∧
    (∃ gs : List (A ⧸ K), Ideal.ofList gs = J.map (Ideal.Quotient.mk K) ∧
      IsRegular (A ⧸ K) gs ∧
      ∀ g ∈ gs, g ∈ (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk K)) := by
  sorry

end RingTheory.Sequence
