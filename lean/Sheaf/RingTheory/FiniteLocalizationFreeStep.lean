/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.RingTheory.ConePseudoCoherent
import Sheaf.RingTheory.FiniteHomologyOfMPseudoCoherent

/-! # One descending step in a simultaneous finite free approximation

Source: Stacks Project, Tag 08EE, proof of lemma-lift-pseudo-coherent.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace DerivedCategory

/-- Adjoin one finite free term to improve a simultaneous approximation by one degree.
The transition retains the old terms in degrees at least the old cutoff.

Source: Stacks Project, Tag 08EE, proof of lemma-lift-pseudo-coherent, the descending
construction (blueprint: lem-sc-finite-localization-free-step).

Proof: Form the cone of alpha. At every specified localization its cohomology vanishes
in degrees at least n, by the cone exact sequence and the two approximation hypotheses.
The localized source is a bounded finite free complex. Truncate the bounded above
finite free model of the localized target to obtain (n-1)-pseudo-coherence. The cone
pseudo-coherence theorem (Tag 064R) gives (n-1)-pseudo-coherence of the localized cone;
finite top cohomology (Tag 064S) makes its degree-(n-1) cohomology finite. Choose a
finite generating family at each localization and cycle representatives. Write each
representative as x/f_j^a. Its differential is killed by some power f_j^c. Thus f_j^c x
is a global cycle whose localized cohomology class is the old generator multiplied
by the unit f_j^(a+c). The union of these finite families defines a map from a finite
free A-module P to the global cone cycles, surjective on degree-(n-1) cohomology at
every localization. Define G by retaining F in degrees at least n, adjoining P in
n-1, and setting all lower terms to zero. The cone coordinates define the new map
component and the negative of the new differential. The cycle equation proves the
chain-map and square-zero identities. Inclusion of the old terms defines tau and
commutes with the maps to M. The cone exact sequence gives the improved approximation.
Since n-1 <= b, the upper bound is unchanged. For an empty family choose P=0; a zero
localization contributes no generators. No unit ideal hypothesis is used.
-/
theorem exists_finite_localization_free_step (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℕ) (f : Fin r → A)
    [∀ j : Fin r, HasDerivedCategory.{w} (ModuleCat.{u} (Localization.Away (f j)))]
    (hlocal : ∀ j : Fin r, IsPseudoCoherent
      (Q.obj ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
        (ComplexShape.up ℤ)).obj M)))
    (b n : ℤ) (hn : n ≤ b + 1)
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (α : F ⟶ M)
    (hupper : F.IsStrictlyLE b) (hlower : F.IsStrictlyGE n)
    (hfinite : ∀ i : ℤ, Module.Free A (F.X i) ∧ Module.Finite A (F.X i))
    (hiso : ∀ j : Fin r, ∀ i : ℤ, n < i → QuasiIsoAt
      ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
        (ComplexShape.up ℤ)).map α) i)
    (hepi : ∀ j : Fin r, Epi (HomologicalComplex.homologyMap
      ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
        (ComplexShape.up ℤ)).map α) n)) :
    ∃ (G : CochainComplex (ModuleCat.{u} A) ℤ) (β : G ⟶ M),
      G.IsStrictlyLE b ∧ G.IsStrictlyGE (n - 1) ∧
      (∀ i : ℤ, Module.Free A (G.X i) ∧ Module.Finite A (G.X i)) ∧
      (∀ j : Fin r, ∀ i : ℤ, n - 1 < i → QuasiIsoAt
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
          (ComplexShape.up ℤ)).map β) i) ∧
      (∀ j : Fin r, Epi (HomologicalComplex.homologyMap
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
          (ComplexShape.up ℤ)).map β) (n - 1))) ∧
      ∃ τ : F ⟶ G, τ ≫ β = α ∧ ∀ i : ℤ, n ≤ i → IsIso (τ.f i) := by sorry

end DerivedCategory
