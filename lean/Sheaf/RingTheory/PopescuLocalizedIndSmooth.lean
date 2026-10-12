/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.Algebra
import Sheaf.RingTheory.ReducedNoetherianTotalRingFractions
import Sheaf.RingTheory.FilteredColimitSmoothProduct

/-! # Ind-smoothness over a total fraction ring
Source: Stacks Project, Smoothing Ring Maps, Tag 07F5, third paragraph.
-/

@[expose] public section
open CategoryTheory
open scoped nonZeroDivisors
universe u v

/-- The total-fraction localization inherits an ind-smooth presentation from the field case.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07F5, third paragraph.
(blueprint: lem-weil-pbc-popescu-standard-nonzerodivisor-aux-localized-ind).

Proof: A reduced Noetherian ring has finitely many minimal primes. Its total fraction
ring is canonically the product of the localizations at these primes, which are fields
and canonically their residue fields, by reduced_noetherian_total_ring_fractions.
Tensoring this compatible product decomposition with Λ identifies its localization
with the product of the corresponding fibre rings. Localization is base change and
tensor products distribute over finite products. Regularity makes each fibre
Noetherian and geometrically regular. A map from its residue field to the fibre is
flat, and its only fibre is the same algebra, so it is regular. Apply the assumed
field case to each factor. Induct on the number of factors using ind_smooth_prod,
then transport the resulting colimit presentation along the two compatible ring
isomorphisms. Nontriviality ensures there is a minimal prime, so the finite product
is nonempty. The fields have universe u, the fibres and all diagram terms have
universe max u v, and the transported presentation retains this universe. -/
theorem localized_target_is_ind_smooth
    (h : ∀ (k : Type u) (Λ : Type (max u v)) [Field k] [CommRing Λ] [Algebra k Λ]
      [IsNoetherianRing Λ],
      RingHom.IsRegular (algebraMap k Λ) →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} k ↦ Algebra.Smooth k B)
          (CommAlgCat.of k Λ))
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ] [Nontrivial R] [IsReduced R]
    (hreg : RingHom.IsRegular (algebraMap R Λ)) :
    ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} (Localization R⁰) ↦
        Algebra.Smooth (Localization R⁰) B)
      (CommAlgCat.of (Localization R⁰)
        (Localization (Algebra.algebraMapSubmonoid Λ R⁰))) := by
  sorry

