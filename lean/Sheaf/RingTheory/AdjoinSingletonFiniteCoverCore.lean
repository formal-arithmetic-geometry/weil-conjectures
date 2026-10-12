/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.RingTheory.AnalyticallyUnramified
public import Sheaf.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.RingTheory.FiniteOverNagata
import Sheaf.RingTheory.JapaneseDomain
import Sheaf.RingTheory.NagataLocalization

/-! # Structural finite cover for a fractional monogenic algebra
Source: Stacks Project, Algebra, Tag 0334, Step 5. -/

@[expose] public section

universe u v

/-- The splitting-field construction gives a finite cover and monogenic local presentations.
Source: Stacks Project, Algebra, Tag 0334, Step 5, lines 46137--46173.
(blueprint: lem-weil-pbc-monogenic-maximal-finite-cover-core).

Proof: Contract the chosen maximal ideal to R. Zariski's lemma makes the residue of x
algebraic over the contracted residue field. Lift its monic minimal polynomial and invert
one product of coefficient denominators outside the contracted prime. Take a finite
splitting field L of the lifted polynomial and the integral closure R' of the localized R
in L. Nagata finiteness makes R' finite, normal, Noetherian and Nagata, with fraction field
L. The ring R'[x] is finite over the localized R[x]. Localize it at R[x] minus m to obtain
B. Localization preserves finiteness, injectivity and the domain property. At every maximal
ideal of B, integrality identifies its local ring with R'[x] at a maximal ideal over m.
The split polynomial evaluates into that ideal, so some root r satisfies x-r in the ideal.
The equality R'[x]=R'[x-r] gives the stated local presentation with y=x-r. Finally write
x=b/a over the original R. Inverting the nonzero image of a turns R'[x] into R'_a.
The corresponding principal open in B, and all its prime localizations, are normal domains.
The constructions use finite extensions and localizations in Type(max u v), with universe
lifts for R and K if necessary. No analytic-unramified assertion is used here. -/
theorem exists_finite_cover_adjoin_singleton_core
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (hR : IsNagataRing R) (x : K)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : IsDomain B)
      (_ : Algebra (Localization.AtPrime m) B) (_ : IsNoetherianRing B),
      Function.Injective (algebraMap (Localization.AtPrime m) B) ∧
      Module.Finite (Localization.AtPrime m) B ∧
      (∃ f : B, f ≠ 0 ∧ ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
      (∀ (q : Ideal B) [q.IsMaximal],
        ∃ (R' K' : Type (max u v)) (_ : CommRing R') (_ : IsDomain R')
          (_ : IsIntegrallyClosed R') (_ : IsNoetherianRing R') (_ : Field K')
          (_ : Algebra R' K') (_ : IsFractionRing R' K'),
          IsNagataRing R' ∧ ∃ (y : K')
            (_ : IsNoetherianRing (Algebra.adjoin R' ({y} : Set K')))
            (n : Ideal (Algebra.adjoin R' ({y} : Set K'))) (_ : n.IsMaximal),
            (⟨y, Algebra.subset_adjoin (Set.mem_singleton y)⟩ :
              Algebra.adjoin R' ({y} : Set K')) ∈ n ∧
              Nonempty (Localization.AtPrime q ≃+* Localization.AtPrime n)) := by sorry
