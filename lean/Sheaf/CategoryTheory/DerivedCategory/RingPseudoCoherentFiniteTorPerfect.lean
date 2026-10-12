/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.RingTheory.Flat.CategoryTheory
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel

/-! # Pseudo-coherent complexes of finite Tor dimension are perfect

Source: literature/stacks-project/more-algebra.tex, More on Algebra, Lemma 15.76.2
(Tag 0658) (blueprint: lem-pc-ring-pseudo-coherent-finite-tor-perfect).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A pseudo-coherent object `C` of `D(R)` with Tor amplitude in some interval `[a, b]`,
`a ≤ b`, is isomorphic in `D(R)` to a bounded complex of finitely generated projective
`R`-modules, i.e. it is perfect in the affine sense.
Source: Stacks Project, More on Algebra, Lemma 15.76.2 (Tag 0658)
(blueprint: lem-pc-ring-pseudo-coherent-finite-tor-perfect).

Proof: Testing the amplitude with `M = R` gives `H^i(C) = 0` for `i > b`, so `C` is
represented by a complex `P` of finite free modules with `P^i = 0` for `i > b`. `P` is
bounded above and flat, hence K-flat, so `H^i(P ⊗ M) = 0` for all `M` and `i ∉ [a, b]`; with
`M = R`, `H^i(P) = 0` for `i < a`. Put `E = τ_{≥ a} P`, bounded, with `E^a = coker(P^{a-1} →
P^a)` finitely presented and the other terms finite free. As `P^{≤ a}` resolves `E^a`,
`Tor_1(E^a, M) = H^{a-1}(P ⊗ M) = 0` for every `M`, so `E^a` is flat, hence finite projective.
The surjection `P → E` is a quasi-isomorphism, so `C ≅ E` with `E` a bounded complex of finite
projective modules. -/
theorem isPerfect_of_pseudoCoherent_finiteTorAmplitude
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (C : DerivedCategory (ModuleCat.{u} R)) (hPC : IsPseudoCoherent C)
    (hTor : ∃ a b : ℤ, a ≤ b ∧ torAmplitudeIn (ModuleCat.{u} R) a b C) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite R (P.X n)) ∧
      (∀ n : ℤ, Module.Projective R (P.X n)) ∧
      Nonempty (Q.obj P ≅ C) := by
  sorry

end DerivedCategory
