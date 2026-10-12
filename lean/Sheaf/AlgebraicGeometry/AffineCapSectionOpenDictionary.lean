/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Sheaf.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.Paper.NonvanishingSectionTrivializes
import Sheaf.RingTheory.AffineFiniteProjectivePrimeMembership
import Sheaf.RingTheory.FiniteProjectiveOfStandardCover

/-! # Affine dictionary for an invertible module and its section

Source: literature/stacks-project/schemes.tex, Schemes, Lemmas 01IA and 01IB,
together with Modules, Lemma 01CY (blueprint: lem-sc-affine-cap-section-open-dictionary).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.QuasicoherentTilde

namespace AlgebraicGeometry.Scheme.Modules

/-- The affine dictionary for an invertible module and a section of it.

Source: literature/stacks-project/schemes.tex, Schemes, Lemmas 01IA and 01IB,
together with Modules, Lemma 01CY (blueprint: lem-sc-affine-cap-section-open-dictionary).
Proof.
1. An invertible module is quasi-coherent. The affine tilde/Gamma counit
   (`lem-weil-pbc-affine-tilde-gamma-adjunction`) identifies M with tilde(Gamma(X,M)).
2. Local rank-one trivializations (`def-sc-invertible-module`) refine to standard opens.
   Quasi-compactness (`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`) gives a
   finite cover by D(f_i). On each member, `lem-weil-pbc-spec-module-tilde-sections`
   identifies N localized at f_i with R localized at f_i. The finite-cover converse
   `lem-sc-affine-standard-cover-finite-projective` makes N finite projective.
   Localizing one trivialization containing p gives N_p isomorphic to R_p.
3. `lem-weil-pbc-spec-tilde-stalk-localization` identifies M_p with N_p and the germ
   of s with s/1. Apply `lem-sc-affine-finite-projective-prime-membership` to obtain
   the displayed membership equivalence. The maximal ideal of R_p is pR_p, so
   the stalk criterion in `lem-weil-pbc-nonvanishing-section-trivializes` identifies
   the actual nonvanishing locus of s with the displayed prime-membership set.
-/
theorem affine_cap_section_open_dictionary
    {R : Type u} [CommRing R]
    (M : (Spec (.of R)).Modules) [M.IsInvertible]
    (s : ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)) :
    IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) M) ∧
      (Module.Finite R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M) ∧
        Module.Projective R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)) ∧
      (∀ (p : Ideal R) [p.IsPrime],
        Nonempty
            (((LocalizedModule p.primeCompl
                ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)) ≃ₗ[Localization.AtPrime p]
              (Localization.AtPrime p))) ∧
        (LocalizedModule.mk s 1 ∈
            (Ideal.map (algebraMap R (Localization.AtPrime p)) p) •
              (⊤ : Submodule (Localization.AtPrime p)
                (LocalizedModule p.primeCompl
                  ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M))) ↔
          s ∈ p •
            (⊤ : Submodule R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)))) ∧
      (nonvanishingLocus M s =
        {p : PrimeSpectrum R |
          ¬ s ∈ p.asIdeal •
            (⊤ : Submodule R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M))}) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
