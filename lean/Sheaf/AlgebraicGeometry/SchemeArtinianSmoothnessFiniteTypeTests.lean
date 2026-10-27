/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Length
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Sheaf.RingTheory.ArtinianFiniteTypeResidueCriterion
import Sheaf.AlgebraicGeometry.SmoothFixedResidueArtinianTest

/-! # Scheme smoothness from finite type Artinian tests

Source: Stacks Project, More on Morphisms, Tag 02HY, implication (2) to (1)
(blueprint: lem-sfb-scheme-artinian-smoothness-finite-type-tests).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Lifting small Artinian extensions with finite type bottom maps detects smoothness.
The kernel is required to be square zero and to have length one. There is no
residue-field restriction and no separation or quasi-compactness assumption on `f`.

Source: Stacks Project, More on Morphisms, Tag 02HY, implication (2) to (1)
(blueprint: lem-sfb-scheme-artinian-smoothness-finite-type-tests).

Proof following the four steps of the node:
1. Fix a finite type point `w` of `W`. For affine `D = Spec R` around `f(w)` and
   affine `U = Spec A` around `w` in its preimage, factor the residue-field point
   through `U` (lem-weil-pbc-affine-opens-basis,
   lem-weil-pbc-morphism-factors-through-open-subscheme). By
   lem-weil-pbc-lft-affine-pairs, `A` is finite type over `R` and `κ(w)` over `A`;
   adjoining the two finite lists of generators makes `κ(w)` finite type over `R`
   (lem-sfb-finite-type-points-detect-open supplies the finite type point notion).
2. In a fixed-residue Artinian test at `w`, the bottom map `c` has one-point source
   (lem-weil-pbc-artinian-local-unique-prime). Factor it through each affine open
   containing `f(w)` (lem-weil-pbc-morphism-factors-through-open-subscheme,
   def-weil-affine-spectrum). Its residue map is the map of step 1, so
   lem-sfb-artinian-finite-type-residue-criterion makes its coordinate ring finite
   type over `R`. Other affine opens have empty preimage. These computations give
   local finite type and quasi-compactness, hence finite type for `c`
   (def-weil-finite-type-morphism).
3. A length-one kernel `I` is simple: an intermediate nonzero proper submodule
   would give a chain of length two (def-weil-pbc-module-length). A nonzero
   generator identifies `I` with the residue field of the local ring `B'`, so its
   maximal ideal annihilates `I`. As `I` is proper, it lies in that maximal ideal;
   hence `I² = 0`. Step 2 makes `c` finite type, so the hypothesis gives every
   fixed-residue lift at `w`. Apply lem-sfb-smooth-fixed-residue-artinian-test to
   obtain a smooth open neighbourhood of `w`.
4. The union of all source opens on which `f` is smooth contains every finite type
   point. By lem-sfb-finite-type-points-detect-open this union is all of `W`.
   Apply lem-weil-pbc-smooth-local-on-source. For empty `W`, use the empty cover.
-/
theorem smooth_of_artinian_lifting_finite_type_tests
    {W V : Scheme.{u}} (f : W ⟶ V) [LocallyOfFiniteType f]
    [IsLocallyNoetherian V]
    (hlift : ∀ (B' B : CommRingCat.{u})
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (q : B' ⟶ B), Function.Surjective q.hom →
      (RingHom.ker q.hom) ^ 2 = ⊥ →
      Module.length B' (RingHom.ker q.hom) = 1 →
      ∀ (b : Spec B ⟶ W) (c : Spec B' ⟶ V),
        b ≫ f = Spec.map q ≫ c →
        LocallyOfFiniteType c → QuasiCompact c →
        ∃ b' : Spec B' ⟶ W, Spec.map q ≫ b' = b ∧ b' ≫ f = c) :
    Smooth f := by
  sorry

end AlgebraicGeometry
