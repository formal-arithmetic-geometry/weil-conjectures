/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Sheaf.FieldTheory.SeparableExtension
public import Sheaf.RingTheory.SingularIdeal
import Sheaf.RingTheory.RegularLocalSeparableResidueSmooth

/-!
# Smoothness at the generic point over a field

Source: Stacks Project, Algebra, Lemma 07ND, separable fraction field implies smoothness,
specialized to a field base; Lemma 00TV and Definition 00TB
(blueprint: lem-weil-pbc-smooth-at-generic-point-over-field).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- A finite type domain over a field with separable fraction field is smooth at the zero prime.
Here `IsSmoothAtPrime` means that there is a nonzero `g : S` with `Localization.Away g`
smooth over `k`, as in Stacks Project, Algebra, Definition 00TB.
Source: Stacks Project, Algebra, Lemma 07ND, the reverse implication with field base
(blueprint: lem-weil-pbc-smooth-at-generic-point-over-field).

Proof, step 1: localization of the domain at the zero prime is its fraction field `L`,
and its residue field is also `L` (`def-weil-pbc-localization-at-prime`). A field is
regular local (`lem-weil-pbc-field-regular-ring`), and the residue extension is separable
by `hsep` (`def-weil-pbc-separable-field-extension`).
Step 2: apply `lem-weil-pbc-regular-local-separable-residue-smooth`, the regular-to-smooth
direction of Stacks 00TV, using finite type, regularity, and separability from step 1.
This gives smoothness at the zero prime (`def-weil-pbc-singular-ideal`), namely a
principal localization at a nonzero element which is smooth over `k`
(`def-weil-pbc-smooth-ring-map`). -/
theorem smoothAtPrime_bot_of_isSeparable_fractionRing
    (k : Type u) (S : Type v) (L : Type w)
    [Field k] [CommRing S] [IsDomain S] [Field L]
    [Algebra k S] [Algebra S L] [Algebra k L] [IsScalarTower k S L]
    [FiniteType k S] [IsFractionRing S L] (hsep : IsSeparableExtension k L) :
    IsSmoothAtPrime k (⟨(⊥ : Ideal S), inferInstance⟩ : PrimeSpectrum S) := by
  sorry

end Algebra
