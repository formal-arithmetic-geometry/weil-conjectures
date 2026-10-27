/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import WeilConjectures.RingTheory.PolynomialTorBound

/-! # Tor bounds for polynomial modules flat over the base

Source: Stacks Project, more-algebra.tex, Tag 068X (polynomial Tor-bound input)
and Section 06XY (derived tensor); algebra.tex, Tags 00HD and 00M3;
Weibel, Theorem 4.3.7, via `ModuleCat.polynomial_tor_bound_of_base_tor_bound`.
(blueprint: lem-trf-base-flat-polynomial-tor-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ModuleCat

/-- A polynomial module flat over its coefficient ring has ordinary base Tor zero in
positive degrees and polynomial Tor zero above the number of variables. Its base derived
tensor with any module in degree zero is the ordinary tensor in degree zero.
No finite-generation or Noetherian assumptions are imposed.

Source: Stacks Project, more-algebra.tex, Tag 068X (polynomial Tor-bound input),
Section 06XY (derived tensor); algebra.tex, Tags 00HD and 00M3; Weibel, Theorem 4.3.7.
(blueprint: lem-trf-base-flat-polynomial-tor-bound).

Proof (the node's three steps):
1. Restrict M along the coefficient map. By lem-weil-pbc-flat-tensor-exact its tensor
   functors preserve exact sequences. The complex M[0] is bounded above with flat terms,
   including the zero terms, so lem-pc-module-bounded-flat-kflat makes it K-flat, in the
   equivalent categorical convention of def-pc-module-kflat-complex. Apply
   lem-pc-source-kflat-module-tensor-model with first complex M[0] and second complex L[0].
   Their total tensor has only its degree-zero term M tensor_R L, and zero differentials,
   giving the first conclusion without any flatness assumption on L.
2. Resolve L by projective modules as in def-weil-pbc-tor-modules. Exactness in positive
   degrees survives tensoring with M by lem-weil-pbc-flat-tensor-exact. Thus ordinary
   Tor_j(L,M) vanishes for j>0. The symmetry of lem-weil-pbc-tor-symmetry gives the specified
   first-variable Tor_j(M,L) vanishing, independently of the derived-category computation.
3. Apply lem-pc-polynomial-tor-bound with base R and d=0. Step 2 supplies its base Tor
   hypothesis, so it gives Tor_j(M,N)=0 over the polynomial ring for j>n. None of these
   arguments requires finite generation or a Noetherian ring. For n=0 the polynomial ring
   is canonically R; for M=0 all tensors vanish; over the zero ring every unital module
   is zero. -/
theorem base_flat_polynomial_tor_bound
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (n : ℕ) (M : ModuleCat.{u} (MvPolynomial (Fin n) R))
    (hflat : Module.Flat R ((restrictScalars MvPolynomial.C).obj M)) :
    (∀ L : ModuleCat.{u} R,
      Nonempty
        (((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            ((restrictScalars MvPolynomial.C).obj M)) ⊗
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj L) ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (((restrictScalars MvPolynomial.C).obj M) ⊗ L))) ∧
      (∀ (L : ModuleCat.{u} R) (j : ℕ), 0 < j →
        IsZero (((Tor' (ModuleCat.{u} R) j).obj
          ((restrictScalars MvPolynomial.C).obj M)).obj L)) ∧
      (∀ (N : ModuleCat.{u} (MvPolynomial (Fin n) R)) (j : ℕ), n < j →
        IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin n) R)) j).obj M).obj N)) := by
  sorry

end ModuleCat
