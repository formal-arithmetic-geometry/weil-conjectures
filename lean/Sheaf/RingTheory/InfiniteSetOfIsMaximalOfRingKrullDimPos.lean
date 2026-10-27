/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic

import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Infinitely many maximal ideals in a positive-dimensional finite type domain

Source: Stacks Project, Algebra, Tags 00G1 and 00FV, affine positive-dimension argument
(blueprint: lem-sc-fg-domain-positive-dimension-infinite-maximals).
-/

@[expose] public section

universe u v

namespace Algebra.FiniteType

/-- A finite type domain over a field with positive Krull dimension has infinitely many
maximal ideals. Source: Stacks Project, Algebra, Tags 00G1 and 00FV, affine
positive-dimension argument (blueprint: lem-sc-fg-domain-positive-dimension-infinite-maximals).

Proof: suppose that there are only finitely many maximal ideals. If the domain is not a
field, each maximal ideal is nonzero; choose a nonzero element in each and multiply them.
The product is nonzero because the ring is a domain, and belongs to every maximal ideal.
The finite type algebra is Jacobson by Tag 00G1, so the prime ideal zero is the intersection
of all maximal ideals (`lem-weil-pbc-finite-type-over-field-prime-intersection-maximal`).
The product must therefore be zero, a contradiction. The empty set of maximal ideals is
excluded by maximal-ideal existence for the proper ideal zero
(`lem-weil-pbc-proper-ideal-contained-in-maximal`). Thus the domain would be a field.
A field has just the zero prime ideal and hence Krull dimension zero, contradicting the
positive-dimension hypothesis. Therefore the set of maximal ideals is infinite. -/
theorem infinite_setOf_isMaximal_of_ringKrullDim_pos
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IsDomain A] (hdim : 0 < ringKrullDim A) :
    Set.Infinite {m : Ideal A | m.IsMaximal} := by
  classical
  by_contra h
  have hfin : Set.Finite {m : Ideal A | m.IsMaximal} := Set.not_infinite.mp h
  have hJ : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hinf : hfin.toFinset.inf (fun m ↦ m) = (⊥ : Ideal A) := by
    calc
      _ = sInf (↑hfin.toFinset : Set (Ideal A)) := Finset.inf_id_eq_sInf _
      _ = (⊥ : Ideal A).jacobson := by
        simp only [Set.Finite.coe_toFinset, Ideal.jacobson, bot_le, true_and]
      _ = ⊥ := isJacobsonRing_iff_prime_eq.mp hJ _ Ideal.isPrime_bot
  -- Primality of a finite intersection forces equality with one of its factors.
  have hp : (hfin.toFinset.inf (fun m ↦ m)).IsPrime := hinf.symm ▸ Ideal.isPrime_bot
  obtain ⟨m, hm, heq⟩ := Ideal.eq_inf_of_isPrime_inf hp
  have hmmax : m.IsMaximal := hfin.mem_toFinset.mp hm
  have hbot : (⊥ : Ideal A).IsMaximal := (heq.trans hinf) ▸ hmmax
  have hfield : IsField A := Ring.isField_iff_maximal_bot.mpr hbot
  exact (ne_of_gt hdim) (ringKrullDim_eq_zero_of_isField hfield)

end Algebra.FiniteType
