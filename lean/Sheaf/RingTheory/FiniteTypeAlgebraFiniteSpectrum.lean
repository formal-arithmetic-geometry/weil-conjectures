/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Finite-type algebras with finite spectrum

Source: literature/stacks-project/algebra.tex, Lemmas 00KH and 0ALW
(blueprint: pqf-lem-finite-type-algebra-finite-spectrum).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite-type algebra over a field with finite prime spectrum is finite-dimensional,
with discrete spectrum and only maximal prime ideals.

Source: Stacks Project, Algebra, Lemma 0ALW (Tag 0ALW), together with Lemma 00KH
(Tag 00KH) (blueprint: pqf-lem-finite-type-algebra-finite-spectrum).

Proof: The finite-spectrum finite-type field-algebra lemma
`Ideal.isMaximal_of_finite_primeSpectrum_of_finiteType`
(lem-pqf-finite-spectrum-maximal-primes) gives maximality of every prime.
The finite-type dimension-zero finiteness lemma
`Module.finite_iff_krullDimLE_zero` (lem-weil-pbc-finite-type-algebra-dim-zero-finite),
with dimension at most zero supplied by `Ring.KrullDimLE.mk₀`, gives `Module.Finite k B`.
The base field is Artinian, as required by that lemma. Finally, a spectrum point is
closed exactly when its prime is maximal, so step 1 makes every singleton closed.
By finiteness, the complement of any singleton is a finite union of closed
singletons and is closed. Every singleton is therefore open, and the spectrum
is discrete. The zero ring has empty spectrum and is the zero-dimensional
vector space over `k`, so all three conclusions hold in that case as well.
-/
theorem finiteType_finiteSpectrum
    (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (hfin : Finite (PrimeSpectrum B)) :
    (∀ p : PrimeSpectrum B, p.asIdeal.IsMaximal) ∧ Module.Finite k B ∧
      DiscreteTopology (PrimeSpectrum B) := by
  sorry

end Algebra
