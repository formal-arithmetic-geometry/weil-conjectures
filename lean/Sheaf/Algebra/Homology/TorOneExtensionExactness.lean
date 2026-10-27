/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.ULift
import WeilConjectures.Algebra.Homology.FreeResolutionSesSplit
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# Exactness at the middle first Tor module of an extension

Source: Stacks Project, Algebra, Tag 00M0, `lemma-long-exact-sequence-tor`,
with the module arguments exchanged
(blueprint: lem-sfb-tor-one-extension-exactness).
-/

@[expose] public section

set_option autoImplicit false

universe r a b c m

namespace CategoryTheory

/-- First-variable Tor in degree one is exact at the middle term of a short exact sequence.
Source: Stacks Project, Algebra, Tag 00M0, `lemma-long-exact-sequence-tor`, with the
module arguments exchanged (blueprint: lem-sfb-tor-one-extension-exactness).

The ring and all four modules are lifted to one common universe; the
displayed maps are the given maps conjugated by these canonical linear equivalences.
Thus the independent ring and module universes impose no size restriction. `Tor'` derives tensor
in the first variable, as in `def-weil-pbc-tor-modules`.

Proof plan:
1. Apply `lem-weil-pbc-free-resolution-ses-split` to choose free resolutions of A, B, C
   with augmentation-compatible lifts of f, g and degreewise splitting maps. Their
   identities are gf = 0, pf = 1, gs = 1 and fp + sg = 1 at each degree. The choice
   is independent of M (Stacks Tag 065P).
2. Tensor these resolutions, lifts and splitting maps with M. Composition and addition
   of tensor maps preserve the four identities, as checked on pure tensors. Consequently
   the resulting sequence of complexes is degreewise short exact without flatness of M.
3. Work in the abelian module category (`lem-weil-pbc-ring-modules-grothendieck-abelian`).
   Reindex the chain complexes as cochain complexes in nonpositive degrees, with zero
   terms in positive degrees. Apply `lem-weil-pbc-complex-ses-homology-long-exact` in
   degree -1: H^(-1) is H_1 of the original chain complex, so the resulting sequence
   of three first homology modules is exact at its middle term (Stacks Tag 0117).
4. Identify these homology modules with Tor by `def-weil-pbc-tor-modules`. Clause (1)
   of `lem-weil-pbc-tor-map-via-resolution-lift` identifies the induced maps with
   Tor_1(f,M) and Tor_1(g,M). A kernel element transports to a homology kernel element,
   has a preimage by step 3, and transports back to a Tor preimage. Conversely the
   composite is zero, by the same naturality identities and injectivity of the canonical
   Tor-to-homology isomorphism. This proves both inclusions of kernel and image.
-/
theorem tor_one_extension_exact
    {R : Type r} [CommRing R]
    {A : Type a} [AddCommGroup A] [Module R A]
    {B : Type b} [AddCommGroup B] [Module R B]
    {C : Type c} [AddCommGroup C] [Module R C]
    (M : Type m) [AddCommGroup M] [Module R M]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact
      (((Tor' (ModuleCat (ULift.{max r a b c m} R)) 1).map
        (ModuleCat.ofHom
          ((ULift.moduleEquiv :
            ULift.{max r a b c m} B ≃ₗ[ULift.{max r a b c m} R] B).symm.toLinearMap.comp
            ((f.restrictScalars (ULift.{max r a b c m} R)).comp (ULift.moduleEquiv :
              ULift.{max r a b c m} A ≃ₗ[ULift.{max r a b c m} R] A).toLinearMap)))).app
        (ModuleCat.of (ULift.{max r a b c m} R) (ULift.{max r a b c m} M))).hom
      (((Tor' (ModuleCat (ULift.{max r a b c m} R)) 1).map
        (ModuleCat.ofHom
          ((ULift.moduleEquiv :
            ULift.{max r a b c m} C ≃ₗ[ULift.{max r a b c m} R] C).symm.toLinearMap.comp
            ((g.restrictScalars (ULift.{max r a b c m} R)).comp (ULift.moduleEquiv :
              ULift.{max r a b c m} B ≃ₗ[ULift.{max r a b c m} R] B).toLinearMap)))).app
        (ModuleCat.of (ULift.{max r a b c m} R) (ULift.{max r a b c m} M))).hom := by
  sorry

end CategoryTheory
