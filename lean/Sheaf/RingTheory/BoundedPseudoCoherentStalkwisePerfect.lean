/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.CategoryTheory.DerivedCategory.PerfectScalarExtension
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.RingTheory.PerfectPrincipalCoverGlue

/-! # Perfectness from perfect prime localizations

Source: Stacks Project, More on Algebra, Tag 068W, lemma-check-perfect-stalks,
implication (2) to (1) in the bounded-below case
(blueprint: lem-sfb-bounded-pseudocoherent-stalkwise-perfect).
-/

@[expose] public section

set_option autoImplicit false

universe u w wq

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A bounded-below pseudo-coherent object is perfect when its scalar extension to every
prime localization is perfect. The scalar extension is the fixed-second-factor K-flat
construction evaluated at the regular localized module in degree zero. Local perfect
models may have different bounds; the ring need not be Noetherian.

Source: Stacks Project, More on Algebra, Tag 068W, lemma-check-perfect-stalks,
implication (2) to (1) under the bounded-below hypothesis
(blueprint: lem-sfb-bounded-pseudocoherent-stalkwise-perfect).

Proof:
1. By def-pc-ring-pseudo-coherent-complex choose a bounded-above finite-free model F.
   Its terms are flat, so lem-pc-module-bounded-flat-kflat makes F and its prime
   localizations K-flat. By lem-pc-derived-tensor-second-factor-functor their ordinary
   tensor complexes compute the derived scalar extensions. The balanced maps
   (x tensor u) tensor v |-> x tensor uv and x tensor v |-> (x tensor 1) tensor v
   identify extension to a residue field with extension first to the prime localization
   and then to that residue field, as an isomorphism in the derived category.
2. By lem-sc-perfect-pullback-perfect-residue each residue fibre is perfect, hence has
   cohomology zero below some integer a_q. This integer may depend on the prime q.
3. Apply lem-sfb-bounded-pseudocoherent-residue-model with the global cohomology lower
   bound and the residue lower bound a_q. It supplies f_q outside q and a bounded
   finite-free model over B[1/f_q]. This makes that scalar extension perfect.
4. By lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact the principal opens D(f_q)
   admit a finite subcover, whose defining elements generate the unit ideal. Apply
   lem-weil-pbc-perfect-ring-principal-cover-glue to conclude perfectness over B.
   The empty cover includes the zero ring; no uniform primewise bound is assumed. -/
theorem isPerfectRingComplex_of_boundedBelow_pseudoCoherent_stalkwisePerfect
    {B : Type u} [CommRing B] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [∀ q : PrimeSpectrum B,
      HasDerivedCategory.{wq} (ModuleCat.{u} (Localization.AtPrime q.asIdeal))]
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : IsPseudoCoherent K)
    (hbounded : ∃ c : ℤ, ∀ i : ℤ, i < c →
      IsZero ((homologyFunctor (ModuleCat.{u} B) i).obj K))
    (hlocal : ∀ q : PrimeSpectrum B,
      IsPerfectRingComplex
        (((Classical.choose (exists_derivedTensor_second_factor_functor
            (algebraMap B (Localization.AtPrime q.asIdeal))).2).obj
          ((HomologicalComplex.single (ModuleCat.{u} (Localization.AtPrime q.asIdeal))
            (ComplexShape.up ℤ) 0).obj
            (ModuleCat.of (Localization.AtPrime q.asIdeal)
              (Localization.AtPrime q.asIdeal)))).obj K)) :
    IsPerfectRingComplex K := by
  sorry

end DerivedCategory
