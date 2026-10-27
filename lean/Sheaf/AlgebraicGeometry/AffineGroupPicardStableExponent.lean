/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.CharacterPicardIsogenySequence

/-! # A field-uniform Picard exponent for an affine algebraic group

Source: Brion, On Linearization of Line Bundles (2015), Lemma 2.3 and
Proposition 2.5, pp.117--119; Milne, Algebraic Groups (2017), Corollary 18.23.
(blueprint: lem-sfb-affine-group-picard-stable-exponent)

One positive exponent trivializes every invertible module after every field extension.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

/-- A smooth connected affine finite-type group over an algebraically closed field has
one positive tensor exponent that trivializes every invertible module over every extension.
Source: Brion, On Linearization of Line Bundles (2015), Lemma 2.3 and Proposition 2.5,
pp.117--119; Milne, Algebraic Groups (2017), Propositions 18.18 and 18.22,
Corollary 18.23, pp.391--393.
(blueprint: lem-sfb-affine-group-picard-stable-exponent)

Proof plan:
1. By lem-sfb-picard-trivial-multiplicative-cover choose a smooth connected affine
   group P and a multiplicative isogeny P → G with Pic(P) = 0. Its finite diagonalizable
   scheme-theoretic kernel is D(M) for a finite abelian group M. These choices are over k.
2. For each m in M, repetition among 0,m,...,|M|m gives a positive r_m ≤ |M| with
   r_m m = 0. The product n of the r_m is positive and annihilates M. On the Hopf
   algebra k[M], multiplication by n sends e^m to e^(nm) = 1. Thus [n] on D(M) is
   trivial even for nonreduced kernels, and n kills every character of D(M).
3. By lem-sfb-character-picard-isogeny-sequence the character connecting homomorphism
   onto Pic(G) is surjective, since Pic(P) = 0. Its additivity shows n Pic(G) = 0.
4. For any field extension K/k, lem-sfb-affine-group-picard-field-invariance identifies
   Pic(G) with Pic(G_K) by pullback. Lift the class of N, apply step 3 and pull back:
   n[N] = 0, which means N.tensorPow n is isomorphic to the structure sheaf.
   The same n precedes K and N, with no algebraicity, separability or perfection
   hypothesis on the extension. The construction includes the trivial group.
-/
theorem affineGroup_picard_stable_exponent
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G]
    [Smooth G.hom] [ConnectedSpace G.left] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ n : ℕ, 1 ≤ n ∧
      ∀ (K : Type u) [Field K] [Algebra k K]
        (N : (pullback G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules),
        N.IsInvertible → Nonempty (N.tensorPow n ≅ 𝟙_ _) := by
  sorry

end AlgebraicGeometry
