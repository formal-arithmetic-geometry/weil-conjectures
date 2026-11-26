/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Artinian.Defs
import WeilConjectures.RingTheory.ArtinianTranscendentalLocalizationProperties
import WeilConjectures.RingTheory.ArtinianTranscendentalLocalizationEvaluation

/-!
# The polynomial localization for a transcendental residue element

For a local map `D → S` of Artinian local rings and `x ∈ S` with transcendental residue,
localizing `D[t]` at the inverse image of the maximal ideal of `S` gives an Artinian local,
essentially smooth factorization `D → D[t]_P → S` sending `t` to `x`.

## Implementation details

Transcendence gives `P = m_D[t]`, so `T = D[t]_P` is Noetherian local with nilpotent maximal
ideal, hence Artinian. Evaluation at `x` extends to `T → S` by the universal property of
localization, and is flat by the fibre criterion since `T/m_D T = F(t)` is a field. The
statement uses the universe lift of `T`. Injectivity of evaluation at `x` is not needed.

## References

* [Stacks, Tag 07FI] (Smoothing Ring Maps, proof, transcendental case)
* [Stacks, Tag 00MP]
-/

@[expose] public section

set_option autoImplicit false
universe u v z

namespace Algebra

/-- Localizing D[t] at the inverse image of the target maximal ideal gives an Artinian
local essentially smooth factorization when the residue of x is transcendental. -/
theorem artinian_transcendental_polynomial_localization
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (hflat : (algebraMap D S).Flat) (x : S)
    (hx : Transcendental (IsLocalRing.ResidueField D) (IsLocalRing.residue S x)) :
    let P : Ideal (Polynomial D) :=
      (IsLocalRing.maximalIdeal S).comap (Polynomial.eval₂RingHom (algebraMap D S) x)
    letI : P.IsPrime := inferInstance
    let T := ULift.{max u v z} (Localization.AtPrime P)
    IsLocalRing T ∧ IsArtinianRing T ∧ IsLocalHom (algebraMap D T) ∧ EssentiallySmooth D T ∧
      ∃ g' : T →+* S, IsLocalHom g' ∧ g'.Flat ∧
        g'.comp (algebraMap D T) = algebraMap D S ∧ x ∈ Set.range g' := by
  dsimp
  have hs := localization_artinian_transcendental_properties D S hflat x hx
  have he := localization_transcendental_evaluation D S hflat x hx
  rcases hs with ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4, he⟩

end Algebra
