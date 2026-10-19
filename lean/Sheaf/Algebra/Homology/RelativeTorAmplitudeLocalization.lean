/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.RingTheory.Ideal.Maximal
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-!
# Relative Tor amplitude and simultaneous prime localization

Source: Stacks Project, More on Algebra, Tag 0B67, lemma-tor-amplitude-localization,
equivalence of (1) and (2) (blueprint: lem-trf-relative-tor-amplitude-localization).
The base ring of the source is named `R` and its algebra is named `A` here.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

/-- Relative Tor amplitude of an arbitrary algebra-module complex can be tested after
simultaneously localizing the algebra and the base at every algebra prime and its contraction.
Source: Stacks Project, More on Algebra, Tag 0B67, equivalence of (1) and (2).
(blueprint: lem-trf-relative-tor-amplitude-localization)

Proof:
1. Resolve the test module N[0] by a K-flat R-complex P, using
   lem-pc-source-module-kflat-resolution. Resolve the restricted K over R as well.
   The two-resolution comparison lem-pc-source-kflat-module-tensor-model identifies
   K tensor P with the derived tensor. Multiplication on K gives its cohomology an
   A-module structure. No assertion that A-K-flatness implies R-K-flatness is used.
2. Exact localization (lem-weil-pbc-localization-module-exact) commutes with cohomology
   (lem-weil-pbc-exact-functor-complex-cohomology), even for unbounded complexes, and
   preserves quasi-isomorphisms.
3. For q over p, extend P to R_p. It remains K-flat by lem-pc-kflat-extension-of-scalars
   and resolves N_p by step 2. The induced base map sends r/t to phi(r)/phi(t).
4. The tensor comparison sends (k tensor x)/s to (k/s) tensor (x/1); its inverse sends
   (k/s) tensor (x/t) to (k tensor x)/(s phi(t)). Fraction relations and tensor balancing
   prove these are inverse maps. They commute with both terms of the signed total
   differential. Common denominators handle each finite sum in the total direct sums.
5. Taking cohomology gives H^i(K tensor-derived N)_q isomorphic to
   H^i(K_q tensor-derived N_p), with tensor bases R and R_p respectively.
6. For the forward implication, restrict any R_p-module L to R and apply step 5.
   Its localization at p is L since every denominator already acts invertibly.
7. Conversely, test the local condition on N_p. All prime localizations of the
   A-module H^i(K tensor-derived N) vanish outside the interval. If a nonzero element
   existed, its proper annihilator would lie in a maximal ideal, by
   lem-weil-pbc-proper-ideal-contained-in-maximal. Vanishing at that prime gives an
   annihilating denominator outside the ideal, a contradiction. Thus the module is zero.
   For the zero algebra every module is zero, including when its prime spectrum is empty.
-/
theorem relative_tensor_homology_vanish_iff_prime_localizations
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [∀ q : PrimeSpectrum A,
      HasDerivedCategory.{w} (ModuleCat.{u} (Localization.AtPrime (q.asIdeal.comap φ)))]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (hab : a ≤ b) :
    (∀ (N : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) ⊗
          (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))) ↔
    ∀ (q : PrimeSpectrum A)
      (L : ModuleCat.{u} (Localization.AtPrime (q.asIdeal.comap φ))) (i : ℤ),
      (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (Localization.AtPrime (q.asIdeal.comap φ))) i).obj
        (DerivedCategory.Q.obj
          ((((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl) ⋙
            ModuleCat.restrictScalars
              (Localization.localRingHom (q.asIdeal.comap φ) q.asIdeal φ rfl)).mapHomologicalComplex
                (.up ℤ)).obj K) ⊗
          (DerivedCategory.singleFunctor
            (ModuleCat.{u} (Localization.AtPrime (q.asIdeal.comap φ))) 0).obj L)) := by
  sorry

end CochainComplex
