/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Local freeness of the first cokernel under universal rank-one H0

Source: Stacks Project, Tags 00O0 and 00NX, local matrix argument.
(blueprint: new-universal-h0-cokernel-local-free)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

/-- The cokernel of the first differential is free at every prime.

Source: Stacks Project, Tags 00O0 (unit-minor calculation) and 00NX
(finite projective modules are free at primes).

Proof: Since the degree-minus-one term is zero, after any scalar extension
H0 is the kernel of the degree-zero differential. At a prime of R the finite
projective source and target become finite free over the local ring A. Test the
hypothesis with its residue field: the matrix has kernel dimension one, hence
an invertible minor of size n-1, where n is the source rank. Row and column
operations reduce it to an identity block and a map A to a finite free module.
Test the hypothesis with A itself: the remaining kernel is isomorphic to A.
Its injection into A is multiplication by some c. This multiplication is
injective. Every entry of the remaining map annihilates c, so every entry is
zero. The localized cokernel is consequently free. Localization is exact, so it
is the localization of the quotient by the global image.
For n=1 the identity block is empty. Rank zero cannot occur over a nonzero
local ring, by the residue-field test. Over the zero ring all modules are zero.
(blueprint: new-universal-h0-cokernel-local-free) -/
theorem universalH0_cokernel_local_free
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hf0 : Module.Finite R (P.X 0))
    (hf1 : Module.Finite R (P.X 1))
    (hp0 : Module.Projective R (P.X 0))
    (hp1 : Module.Projective R (P.X 1))
    (hneg : IsZero (P.X (-1)))
    (hzero : ∀ (B : Type v) [CommRing B] (φ : R →+* B),
      let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
      Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) :
    ∀ (𝔭 : Ideal R) [𝔭.IsPrime], Module.Free (Localization.AtPrime 𝔭)
      (LocalizedModule 𝔭.primeCompl (P.X 1 ⧸ LinearMap.range (P.d 0 1).hom)) := by sorry

end CochainComplex
