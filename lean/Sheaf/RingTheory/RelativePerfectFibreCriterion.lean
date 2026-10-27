/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.RingTheory.FlatModuleAtPrime
import Sheaf.RingTheory.BoundedPseudoCoherentStalkwisePerfect
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Mathlib.Algebra.Module.Projective

/-! # Relative perfection detected by bounded derived residue fibres

Source: Stacks Project, More on Algebra, Tag 0GHJ,
`lemma-bounded-on-fibres-relatively-perfect`
(blueprint: lem-sfb-ring-relative-perfect-fibre-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u wR wA

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

/-- For a flat finitely presented algebra, a pseudo-coherent complex has uniformly bounded
Tor amplitude over the base exactly when it is bounded below and its derived residue fibres
are bounded below. The fibre bound may depend on the prime. The residue field is the
existing `Ideal.ResidueField`, a fraction field of the prime quotient. The tensors here use
the existing K-flat derived monoidal structure; fibre vanishing is tested after forgetting
to the base ring, which reflects zero cohomology.

Source: Stacks Project, More on Algebra, Tag 0GHJ,
`lemma-bounded-on-fibres-relatively-perfect`
(blueprint: lem-sfb-ring-relative-perfect-fibre-criterion).

Proof:
1. A uniform Tor interval gives the lower bound on C by testing with R in degree zero
   and the lower bound on each fibre by testing with its residue field.
2. For the converse choose a finite polynomial presentation P onto A. The monomial basis
   makes P flat and finitely presented over R. Apply
   lem-sfb-flat-fp-quotient-pseudocoherent to restrict C to a pseudo-coherent object L of
   D(P). Restriction preserves cohomology, and L and C have the same restriction to D(R),
   hence the same derived residue fibres.
3. Choose a bounded-above finite-free P-model F for L. Its terms are R-free, so
   lem-pc-module-bounded-flat-kflat makes it a K-flat R-model. At a prime q of P over p
   of R, lem-pc-affine-flat-module-local-criterion makes R_p to P_q flat; the map is local
   by the numerator criterion for its maximal ideals. Its closed fibre is a localization
   of the polynomial ring over k(p): the maps on fractions and clearing coefficient
   denominators give this identification. By
   lem-weil-pbc-polynomial-ring-field-regular-ring it is regular local of finite dimension.
   Localizing F and its residue tensor preserves cohomology, by clearing a denominator
   that kills a differential. Thus the residue tensor of F_q has cohomology in an interval
   whose lower endpoint is the bound at p and whose upper endpoint bounds F.
4. Apply lem-sfb-regular-fibre-local-perfect to R_p to P_q and F_q with this interval.
   Therefore L_q is perfect for every q, with no uniform interval required here.
5. Apply lem-sfb-bounded-pseudocoherent-stalkwise-perfect to L and its global lower bound.
   Obtain a bounded finite-projective P-model Q, supported in some [a,b]. Each term splits
   off a finite free P-module by projectivity, and is therefore R-flat because P is R-free.
   By lem-pc-module-bounded-flat-kflat, Q computes derived tensor with every R-module N.
   The tensor is supported in [a,b], giving the required common Tor interval for L and C.
   If Q is zero, take [0,0]. Neither ring is assumed Noetherian or nonzero. -/
theorem finiteTorAmplitude_iff_boundedBelow_and_residueFibres_boundedBelow
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    (_hflat : (algebraMap R A).Flat) [Algebra.FinitePresentation R A]
    (C : DerivedCategory (ModuleCat.{u} A)) (_hpc : IsPseudoCoherent C) :
    (∃ a b : ℤ, a ≤ b ∧ torAmplitudeIn (ModuleCat.{u} R) a b
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj C)) ↔
    (∃ c : ℤ, ∀ j : ℤ, j < c →
      IsZero ((homologyFunctor (ModuleCat.{u} A) j).obj C)) ∧
    (∀ p : PrimeSpectrum R, ∃ c : ℤ, ∀ j : ℤ, j < c →
      IsZero ((homologyFunctor (ModuleCat.{u} R) j).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj C) ⊗
          (singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R p.asIdeal.ResidueField)))) := by
  sorry

end DerivedCategory
