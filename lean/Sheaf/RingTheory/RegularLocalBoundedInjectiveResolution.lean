/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.RingTheory.RegularLocalFiniteGlobalDimension
import WeilConjectures.RingTheory.ProjectiveResolutionExtCharacterization
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Module.Injective

/-!
# Bounded injective replacement of a regular local ring

Source: Stacks Project, Dualizing Complexes, Tag 0AWX, first assertion of
`lemma-regular-gorenstein`; More on Algebra, Tag 0A5S, `definition-injective-dimension`
(blueprint: lem-trf-regular-local-bounded-injective-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace IsRegularLocalRing

/-- The ring in degree zero has a bounded representative with injective terms.
Source: Stacks Project, Tags 0AWX and 0A5S
(blueprint: lem-trf-regular-local-bounded-injective-resolution).

Proof:
1. Let `d` be the finite Krull dimension of `A`. The regular-local global-dimension
   bound (`lem-weil-pbc-regular-local-finite-gl-dim`) gives projective resolutions
   of length at most `d` for every module.
2. The projective-dimension/Ext characterization
   (`lem-weil-pbc-projective-dimension-ext-characterization`, `def-pc-ext`) gives
   `Ext^i(M,A) = 0` for all modules `M` and all `i >= d+1`, including `M = A/T`.
3. Enough injectives (`lem-weil-pbc-ring-modules-enough-injectives`) and
   `lem-weil-pbc-left-exact-injective-resolution-degree-zero` give an exact
   augmented resolution `A -> I^0 -> I^1 -> ...`. Put `J = ker(d^d)`.
   If `d = 0`, the augmentation identifies `A` with `J`.
4. For an ideal `T` and `u : T -> J`, injectivity of `I^d` extends its composite
   with `J -> I^d` to `f : A -> I^d`. The differential of `f` factors through
   `h : A/T -> I^(d+1)`, a cocycle. By Ext vanishing and
   `lem-weil-pbc-ext-via-injective-resolution`, write `h = d^d g`.
   Then `f - g pi` lands in `J` and extends `u`, where `pi : A -> A/T`.
5. The ideal-extension direction of `lem-sf-baer-criterion` makes `J` injective.
6. Retain the original terms below `d`, replace degree `d` by `J`, and put zero
   elsewhere, corestricting the last differential to the kernel. Exactness gives
   a quasi-isomorphism from `A[0]`; for `d = 0`, use the isomorphism `A -> J`.
   Every term is injective, including the zero terms
   (`def-sp-injective-resolutions`). Localization inverts the quasi-isomorphism
   (`def-weil-abstract-derived-category`). Take the interval `[0,d]`.

`HasDerivedCategory` specifies the chosen localization and its morphism universe.
The zero terms are expressed by `IsZero`, invariant under module isomorphisms. -/
theorem exists_bounded_injective_complex
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] :
    ∃ (a b : ℤ), a ≤ b ∧
      ∃ I : CochainComplex (ModuleCat.{u} A) ℤ,
        (∀ j : ℤ, Injective (I.X j)) ∧
        (∀ j : ℤ, j < a ∨ b < j → IsZero (I.X j)) ∧
        Nonempty ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A A) ≅ DerivedCategory.Q.obj I) := by
  sorry

end IsRegularLocalRing
