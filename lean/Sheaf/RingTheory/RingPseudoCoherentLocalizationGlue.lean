/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.RingTheory.MPseudoCoherent
import Sheaf.RingTheory.RingPseudoCoherent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Gluing pseudo-coherence over a finite standard-open cover

Source: Stacks Project, More on Algebra, Lemma 15.66.14 (Tag 066D), with Definition 064P
and Lemma 064U (blueprint: lem-pc-ring-pseudo-coherent-localization-glue).
-/

universe w₁ w₂ v₁ u₁

open CategoryTheory

namespace DerivedCategory

/-- Pseudo-coherence, including fixed-degree pseudo-coherence, glues under localization at
finitely many elements generating the unit ideal. Rings are commutative, as in Stacks.
Source: Stacks Project, Tag 066D
(blueprint: lem-pc-ring-pseudo-coherent-localization-glue).

Proof:
1. Fix `m`. Exactness of localization identifies localized cohomology with the cohomology of
   the localized complex. The finitely many bounded approximations give a common upper bound
   for local cohomology; unit-ideal generation detects vanishing globally. Induct on the top
   degree minus `m`. If all cohomology in degrees at least `m` vanishes, use
   `lem-pc-ring-m-pseudo-coherent-vanishing-base` (Tag 064W).
2. Otherwise let `n` be the top degree. Each local object is `n`-pseudo-coherent, so
   `lem-sc-finite-cohomology` makes its top cohomology finite. Apply
   `lem-weil-pbc-module-finite-of-localization-span` to obtain global finiteness. Lift a finite
   free surjection onto top cohomology to cycles, obtaining a map `E[-n]` to the complex.
3. Its cone has vanishing cohomology in degrees at least `n`. Localization commutes with this
   cone triangle. The localized `E[-n]` is finite free and bounded. Clause one of
   `lem-pc-ring-pseudo-coherent-distinguished-triangle` (Tag 064R) makes the localized cones
   `m`-pseudo-coherent. Induction gives global `m`-pseudo-coherence of the cone, and clause two
   of the same triangle lemma gives `m`-pseudo-coherence of the original complex.
4. If every localization is pseudo-coherent, apply
   `lem-pc-ring-pseudo-coherent-iff-all-m` (Tag 064U) locally to get every fixed-degree condition,
   use the first assertion for each integer, then apply the same equivalence globally. -/
theorem ringPseudoCoherent_localization_glue
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (m : ℤ) (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁} (Localization.Away (f i)))]
    (hf : Ideal.span (Set.range f) = ⊤) :
    ((∀ i : Fin r, IsMPseudoCoherent m
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M))) →
      IsMPseudoCoherent m (Q.obj M)) ∧
    ((∀ i : Fin r, IsPseudoCoherent
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M))) →
      IsPseudoCoherent (Q.obj M)) := by
  sorry

end DerivedCategory
