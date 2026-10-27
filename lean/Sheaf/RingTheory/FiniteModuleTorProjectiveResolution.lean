/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.RingPseudoCoherent
import Sheaf.Algebra.Homology.DerivedTensorModuleTorComparison

/-! # A finite Tor bound gives a finite projective resolution

Source: Stacks Project, Tags 0658 and 066Q, with the ordinary Tor comparison
from Tags 00LY and 00LZ (blueprint: lem-trf-finite-module-tor-projective-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

/-- A finite module over a Noetherian ring whose first-variable Tor vanishes above
`d ≥ 0` has derived Tor amplitude `[-d, 0]` and an augmented finite-projective
representative supported in exactly that window. The augmentation is a
quasi-isomorphism, with the stated kernel-image equalities, and is itself an
isomorphism when `d = 0`. Its degree-zero derived object is perfect.

Source: Stacks Project, Tags 0658 (specified projective window), 066Q (augmented
resolution), 00LP (finite-free resolution), and 00LY/00LZ (ordinary Tor).
(blueprint: lem-trf-finite-module-tor-projective-resolution).

Proof plan:
1. Apply `lem-weil-pbc-finite-free-resolution-noetherian` and reverse its augmented
   chain resolution into nonpositive cochain degrees. The kernel-image equalities
   identify its cohomology with `M` in degree zero and zero elsewhere. Hence it is
   quasi-isomorphic to `M[0]`, which is pseudo-coherent by
   `def-pc-ring-pseudo-coherent-complex`.
2. For every module `N`, `lem-kun-derived-module-tor-comparison` identifies degree
   `i` cohomology of `M[0] ⊗ᴸ N[0]` with first-variable Tor in degree `-i` when
   `i ≤ 0`, and with zero when `i > 0`. The hypothesis kills degrees `i < -d`.
   No flatness or finiteness is imposed on `N`.
3. Apply `lem-trf-pseudo-coherent-tor-projective-window` with `a = -d`, `b = 0`.
   It gives a finite-projective complex `E` supported in this interval and an
   isomorphism from its image in the derived category to `M[0]`.
4. Apply cohomology to that isomorphism. Since `E¹ = 0`, the quotient map
   `E⁰ → H⁰(E)` followed by `H⁰(E) ≅ M` gives a surjective augmentation `ε`
   with kernel the image of `d_E⁻¹`. Its other components are zero, so it is a
   cochain map and a quasi-isomorphism. Vanishing of negative cohomology gives
   the remaining kernel-image equalities. Vanishing below `-d` also gives
   injectivity at the left end of the reindexed resolution `F_j = E^(-j)`.
   If `d = 0`, `E⁻¹ = 0`, making `ε` injective as well as surjective. The bounded
   finite-projective model gives perfectness by `def-pc-perfect-ring-complex`.
   The argument permits the zero module and zero ring. -/
theorem exists_finite_projective_resolution_of_tor_vanishing
    (S : Type u) [CommRing S] [IsNoetherianRing S]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    (M : ModuleCat.{u} S) [Module.Finite S M] (d : ℤ) (hd : 0 ≤ d)
    (hTor : ∀ (N : ModuleCat.{u} S) (j : ℕ), d < (j : ℤ) →
      IsZero (((Tor' (ModuleCat.{u} S) j).obj M).obj N)) :
    (∀ (N : ModuleCat.{u} S) (i : ℤ), i < -d ∨ 0 < i →
      IsZero ((homologyFunctor (ModuleCat.{u} S) i).obj
        ((singleFunctor (ModuleCat.{u} S) 0).obj M ⊗
          (singleFunctor (ModuleCat.{u} S) 0).obj N))) ∧
    (∃ (E : CochainComplex (ModuleCat.{u} S) ℤ) (ε : E.X 0 ⟶ M)
      (f : E ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj M),
      (∀ i : ℤ, i < -d ∨ 0 < i → IsZero (E.X i)) ∧
      (∀ i : ℤ, Module.Finite S (E.X i) ∧ Module.Projective S (E.X i)) ∧
      f.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom = ε ∧
      QuasiIso f ∧ Function.Surjective ε.hom ∧
      LinearMap.ker ε.hom = LinearMap.range (E.d (-1) 0).hom ∧
      (∀ i : ℤ, i < 0 →
        LinearMap.ker (E.d i (i + 1)).hom = LinearMap.range (E.d (i - 1) i).hom) ∧
      (d = 0 → IsIso ε)) ∧
    IsPerfectRingComplex ((singleFunctor (ModuleCat.{u} S) 0).obj M) := by
  sorry

end DerivedCategory
