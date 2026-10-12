/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.RingTheory.GlobalDimension
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Module
import Sheaf.RingTheory.FiniteFreeResolution
import Sheaf.RingTheory.FiniteProjectivePrimeLocalFree
import Sheaf.RingTheory.ProjectiveResolutionKernelProjective
import Mathlib.RingTheory.Noetherian.Basic

/-! Bounded finite free resolution construction.
(blueprint: stage3-b4-bounded-finite-free-resolution) -/
@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat
/-- Construction from the infinite finite-free resolution and the projective d-th syzygy.
Source: Stacks Project, Algebra, Tag 0CXF.
Proof:
If `d = 0`, the augmentation of the given length-zero projective resolution is an
isomorphism, so `M` is projective. A finite projective module over a local ring is free
(Tag 00NX); put `M` in degree zero, with identity augmentation and zero terms above it.
If `d > 0`, use Tag 00LP to resolve `M` by finite free modules. Let `K` be the kernel
of the map out of degree `d - 1`, using the augmentation when `d = 1`. Tag 00O5 and
the given length bound imply that `K` is projective. Since it is a submodule of a finite
module over a Noetherian ring, it is finite (Tag 00IK), and hence free by Tag 00NX.
Replace the term of degree `d` by `K`, with differential the kernel inclusion, and
put zero modules above degree `d`. Exactness at degree `d - 1` follows from the
kernel-image equality, and at degree `d` from injectivity of the inclusion. Exactness
in lower degrees and surjectivity of the augmentation are inherited. All terms are
projective since they are free, so the augmented complex gives a ProjectiveResolution.
The zero modules are finite and free as well.
(blueprint: stage3-b4-bounded-finite-free-resolution) -/
theorem exists_bounded_finite_free_resolution {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{max u v} R) [Module.Finite R M]
    (d : ℕ) (h : HasProjectiveResolutionLE M d) :
    ∃ P : ProjectiveResolution M,
      (∀ i : ℕ, d < i → IsZero (P.complex.X i)) ∧
      (∀ i : ℕ, Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i)) := by
  sorry
end ModuleCat
