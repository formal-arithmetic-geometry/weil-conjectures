/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.RingTheory.TorKernelBoundaryConstruction

/-!
# Exactness for the constructed kernel connecting map

Source: Stacks Project, Algebra, Tags 00M0 and 00LZ.
-/

@[expose] public section
universe u
open CategoryTheory
open scoped TensorProduct
namespace CategoryTheory

/-- Exactness of the explicit cycle boundary, without any naturality assertion.

Source: Stacks Project, Algebra, Tag 00M0 (proof of the Tor exact sequence),
Tag 00LZ (comparison of resolutions), and Homology, Tag 0111 (connecting map).

Proof: Put K = ker(q). Choose a horseshoe resolution of the short exact sequence
0 → K → F → N → 0, with degreewise split rows, using free resolutions of K and N.
After tensoring with M the rows remain split exact. The homology long exact
sequence gives exactness at H₁ of the right resolution and H₀ of the left one.
Identify H₀ of the left and middle resolutions with K tensor M and F tensor M
by their augmentations and right exactness of tensor. Compare the chosen
projective resolution P of N used in torKernelBoundary with the right horseshoe
resolution by an augmentation-compatible chain map. Lift its degree-zero map to
the middle resolution using the splitting. Composing with the middle augmentation
gives a lift e₀ : P₀ → F of P's augmentation. The connecting map on a tensor
cycle z is the class of a left degree-zero element w whose image is the
differential of that middle lift of z. Applying the left augmentation identifies
this class with (e₀ d₁) tensor 1 evaluated at z, with codomain restricted to K.
The lift e used in torKernelBoundary differs from e₀ by an R-linear map k : P₀ → K.
The difference of the two resulting degree-one maps is k d₁; after tensoring
this vanishes on cycles. Thus the transported horseshoe connecting map is exactly
torKernelBoundary, not just some exact map. Resolution comparison identifies the
preceding homology map with Tor₁(q,M); augmentation compatibility identifies the
following homology map with the kernel inclusion tensor 1. Transport the two
exact pairs along these isomorphisms to obtain the displayed assertions.

This holds also for zero modules, identity surjections (zero kernel), and
nonprojective F: the free resolutions, not F, supply the projectivity.
(blueprint: lem-sc-p1-tor-kernel-boundary-construction-exact) -/
theorem tor_kernel_boundary_construction_exact
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    Function.Exact (((Tor' (ModuleCat.{u} R) 1).map
      (ModuleCat.ofHom q)).app M).hom (torKernelBoundary M F N q hq) ∧
    Function.Exact (torKernelBoundary M F N q hq)
      ((LinearMap.ker q).subtype.rTensor M) := by sorry

end CategoryTheory
