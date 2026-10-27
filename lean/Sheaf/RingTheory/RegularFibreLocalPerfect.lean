/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import WeilConjectures.RingTheory.RegularLocalFiniteGlobalDimension
import Mathlib.CategoryTheory.Monoidal.Tor
import Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence
import Sheaf.RingTheory.PseudoCoherentMaximalFibrePerfect

/-! # Perfection over a flat local map with regular closed fibre

Source: Stacks Project, More on Algebra, Tag 09PC,
lemma-perfect-over-regular-local-ring, residue-field version of assumption (4).
(blueprint: lem-sfb-regular-fibre-local-perfect).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

/-- A pseudo-coherent complex over a flat local algebra with regular closed fibre of
 dimension `d` is perfect with Tor amplitude `[a-d,b]` when its derived tensor over the
 base with the base residue field has cohomology in `[a,b]`. Neither local ring is assumed
 Noetherian. Restriction of scalars is the exact functor on derived module categories,
 and the tensor symbols denote the existing K-flat derived tensor products.

Source: Stacks Project, More on Algebra, Tag 09PC,
lemma-perfect-over-regular-local-ring.
(blueprint: lem-sfb-regular-fibre-local-perfect).

Proof:
1. Choose a bounded-above finite-free B-complex P representing K, using
   def-pc-ring-pseudo-coherent-complex. Flatness of the ring map makes each term
   R-flat; the terms are also B-flat. By lem-pc-module-bounded-flat-kflat, P is
   K-flat over both rings. Put C = B/m_R B and E = P tensor_B C in D(C).
   The termwise isomorphism P tensor_B C = P tensor_R k, with k = R/m_R,
   computes derived scalar extension by lem-pur-derived-change-of-rings.
   The hypothesis therefore bounds the cohomology of E in [a,b].
2. Locality makes ell = B/m_B the residue field of C. The finite-free C-complex
   P tensor_B C is K-flat. On these models, the isomorphism
   (P tensor_B C) tensor_C ell = P tensor_B ell identifies E tensor_C^L ell
   with K tensor_B^L ell, again by lem-pur-derived-change-of-rings.
3. By lem-weil-pbc-regular-local-finite-gl-dim, every C-module has a projective
   resolution of length at most d. Thus Tor_t^C(M,ell) vanishes for t > d,
   for every C-module M, using def-weil-pbc-tor-modules. Only C is Noetherian.
4. Apply lem-kun-bounded-tensor-tor-spectral-sequence to E and ell[0]. Its E2
   page Tor_{-p}^C(H^q(E),ell) vanishes unless -d <= p <= 0 and a <= q <= b.
   Each later page is a subquotient, so all positions of total degree outside
   [a-d,b] vanish. The finite exhaustive separated convergence filtration has
   zero graded quotients there, forcing H^n(E tensor_C^L ell) = 0.
   Step 2 gives the same bound for K tensor_B^L ell.
5. There is only one maximal ideal of B. Since a-d <= b, apply
   lem-weil-pbc-pseudocoherent-maximal-fibre-perfect to K with interval [a-d,b].
   It gives perfectness and the stated vanishing for every B-module N, without
   any Noetherian assumption on B.
-/
theorem isPerfect_and_tensor_homology_vanish_of_regular_closed_fibre
    {R B : Type u} [CommRing R] [CommRing B] [IsLocalRing R] [IsLocalRing B]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} B)]
    (φ : R →+* B)
    (hlocal : (IsLocalRing.maximalIdeal B).comap φ = IsLocalRing.maximalIdeal R)
    (hflat : φ.Flat)
    (hregular : IsRegularLocalRing (B ⧸ (IsLocalRing.maximalIdeal R).map φ))
    (d : ℕ)
    (hd : ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal R).map φ) = (d : WithBot ℕ∞))
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : K.IsPseudoCoherent)
    (a b : ℤ) (hab : a ≤ b)
    (hfibre : ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj
        ((ModuleCat.derivedRestrictScalars φ).obj K ⊗
          (singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))))) :
    K.IsPerfectRingComplex ∧
      ∀ (N : ModuleCat.{u} B) (j : ℤ), (j < a - (d : ℤ) ∨ b < j) →
        IsZero ((homologyFunctor (ModuleCat.{u} B) j).obj
          (K ⊗ (singleFunctor (ModuleCat.{u} B) 0).obj N)) := by
  sorry

end DerivedCategory
