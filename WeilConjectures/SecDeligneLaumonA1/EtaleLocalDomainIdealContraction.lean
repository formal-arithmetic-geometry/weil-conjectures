/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.SecDeligneLaumonA1.FlatQuasifiniteGenericPrimeUnique
import WeilConjectures.RingTheory.Etale.QuasiFiniteAtPrime
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Nonzero ideals in local étale domains meet the base domain

Source: Stacks Project, More on Algebra, Tag 0GS5, lemma-ideal-inverse-nonzero,
case (1), applied to the localization `A` to `C_Q` of an étale ring map
(blueprint: lem-dl-a1-etale-local-domain-ideal-contraction).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

/-- Every nonzero ideal in a domain obtained by localizing an étale algebra at a prime
has nonzero contraction to the base domain.

Source: Stacks Project, More on Algebra, Tag 0GS5, lemma-ideal-inverse-nonzero,
case (1), applied to the localization `A` to `C_Q` of an étale ring map
(blueprint: lem-dl-a1-etale-local-domain-ideal-contraction).

Proof: Étaleness of `Spec C → Spec A` gives that `A → C` is of finite type and
quasi-finite at every prime of `C`, and that `A → C` is flat; composing with the flat
localization `C → C_Q`, the map `A → C_Q` is flat. The flat quasi-finite generic-prime
lemma then says that the zero prime is the unique prime of `C_Q` contracting to zero in
`A`. Suppose no nonzero element of `A` maps into `J`. Then `J` is disjoint from the
image `S` of the nonzero elements of `A`, so prime-ideal separation gives a prime `P`
containing `J` and disjoint from `S`. A nonzero element of `A` in the contraction of
`P` would map into `P ∩ S`, so this contraction is zero; hence `P = 0` and `J ≤ P`
contradicts `J ≠ 0`.
-/
theorem comap_ne_bot_of_etale_localization
    (A C : Type u) [CommRing A] [IsDomain A] [CommRing C] [Algebra A C]
    (h_etale : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A C))))
    (Q : Ideal C) [Q.IsPrime] [IsDomain (Localization.AtPrime Q)]
    (J : Ideal (Localization.AtPrime Q)) (hJ : J ≠ ⊥) :
    ∃ a : A, a ≠ 0 ∧ algebraMap A (Localization.AtPrime Q) a ∈ J := by
  classical
  obtain ⟨hft, hquasi⟩ :=
    Algebra.finiteType_and_isQuasiFiniteAtPrime_of_etale A C h_etale
  have he : Algebra.Etale A C := by
    rw [← RingHom.etale_algebraMap]
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale)).mp h_etale
  have hflat : RingHom.Flat
      ((algebraMap C (Localization.AtPrime Q)).comp (algebraMap A C)) := by
    have hflatC : RingHom.Flat (algebraMap A C) :=
      RingHom.flat_algebraMap_iff.mpr inferInstance
    have hflatQ : RingHom.Flat (algebraMap C (Localization.AtPrime Q)) :=
      RingHom.flat_algebraMap_iff.mpr inferInstance
    exact hflatC.comp hflatQ
  have hgen := RingHom.flat_quasiFinite_genericPrime_unique A C hquasi Q hflat
  by_contra h
  push Not at h
  let S : Submonoid (Localization.AtPrime Q) :=
    (nonZeroDivisors A).map (algebraMap A (Localization.AtPrime Q))
  have hd : Disjoint (J : Set (Localization.AtPrime Q)) S := by
    apply Set.disjoint_left.mpr
    intro x hx hxS
    obtain ⟨a, ha, rfl⟩ := hxS
    exact h a (nonZeroDivisors.ne_zero ha) hx
  obtain ⟨P, hP, hJP, hPS⟩ := J.exists_le_prime_disjoint S hd
  have hcomap :
      P.comap ((algebraMap C (Localization.AtPrime Q)).comp (algebraMap A C)) =
        (⊥ : Ideal A) := by
    apply le_antisymm _ bot_le
    intro a ha
    by_contra ha0
    have ha' : a ≠ 0 := by simpa using ha0
    apply Set.disjoint_left.mp hPS ha
    exact ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha', rfl⟩
  have hP0 := hgen.2 P hP hcomap
  exact hJ (le_bot_iff.mp (hP0 ▸ hJP))

end Ideal
