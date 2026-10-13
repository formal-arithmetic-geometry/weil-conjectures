/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import Sheaf.RingTheory.LimitModuleFinitePresentation
import Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import Sheaf.RingTheory.ColimitEventuallyFlat

/-!
# Noetherian approximation at a flat point

Source: Stacks Project, Algebra, Theorem Tag 00RC, reduction to finite-type integer models.
(blueprint: lem-weil-pbc-flat-point-noetherian-model)
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Module

/-- A flat point of a finitely presented module descends to a Noetherian model.

Source: Stacks Project, Algebra, Theorem Tag 00RC, first reduction paragraph, using
Tags 00R1 and 00R6. (blueprint: lem-weil-pbc-flat-point-noetherian-model)

Proof:
1. Apply `Algebra.limitModuleFinitePresentation` (00R1). If the input universes differ,
   lift the rings and module to a common universe and transport the conclusion back.
   Contract the given prime and its inverse image in R to every stage.
2. Localize the two ring systems and the module system at those contracted primes.
   Localization commutes with the ring colimits. A module fraction comes from a common
   stage; an equality of fractions is witnessed by a multiplier outside the prime and
   an equality which holds at a later stage. Thus the localized module colimit is M_q.
3. The stage rings are Noetherian, since they are finite type over the integers; their
   localizations are Noetherian local rings. The localized modules are finite. The
   canonical tensor base-change isomorphisms of 00R1, localized, give the ring
   localization and module base-change hypotheses of `RingTheory.exists_flat_stage`.
   All transition maps are local, because the later primes contract to the earlier ones.
4. Flatness over R is equivalent to flatness over its localization at the inverse image
   of q. Apply 00R6 to choose a stage flat at the contracted prime; flatness over the
   localized stage base implies flatness over that stage base.
5. Take A, B, N to be this unlocalized stage. The limit base-change isomorphisms of 00R1
   give the pushout A -> B, R -> S and the S-linear equivalence S tensor_B N = M.
   These are the canonical algebra structures and restricted module actions, hence the
   scalar towers commute. This proves precisely the displayed model properties.

This statement supplies a model and flatness at one contracted point; it supplies no
flat neighborhood and makes no claim that a flat point remains flat after base change. -/
theorem exists_noetherian_model_flat_at_prime
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M]
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S M]
    (q : PrimeSpectrum S)
    (hq : Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)) :
    ∃ (A B N : Type (max u v w)) (_ : CommRing A) (_ : CommRing B)
      (_ : Algebra A B) (_ : Algebra A R) (_ : Algebra B S) (_ : Algebra A S)
      (_ : IsScalarTower A B S) (_ : IsScalarTower A R S)
      (_ : AddCommGroup N) (_ : Module A N) (_ : Module B N)
      (_ : IsScalarTower A B N),
      IsNoetherianRing A ∧ Algebra.FiniteType A B ∧ Module.Finite B N ∧
      Algebra.IsPushout A R B S ∧ Nonempty (S ⊗[B] N ≃ₗ[S] M) ∧
      Module.Flat A
        (LocalizedModule (q.asIdeal.comap (algebraMap B S)).primeCompl N) := by sorry

end Module
