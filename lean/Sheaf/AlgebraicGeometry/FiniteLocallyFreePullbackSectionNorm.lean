/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeFunctionNorm
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison

/-! # Norm sections of powers of pulled-back invertible modules

Source: Stacks Project, Divisors, Tags 0BD2 (lemma-finite-locally-free-has-norm),
0BCY (lemma-norm-invertible), and 0BCZ (lemma-norm-map-invertible)
(blueprint: lem-sfb-finite-locally-free-pullback-section-norm).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A section of a positive tensor power of a pulled-back invertible module admits a
section downstairs of degree multiplied by the finite locally free degree. Its
nonvanishing locus consists exactly of points whose entire fibre is nonvanishing.

Source: Stacks Project, Divisors, Tags 0BD2, 0BCY, and 0BCZ
(blueprint: lem-sfb-finite-locally-free-pullback-section-norm).

Proof:
1. Choose the restriction-compatible function norms from
   `lem-sfb-finite-locally-free-function-norm`. On a cover trivializing L, write
   e_i = a_ij e_j. Pull back these frames to E_i using `def-pc-module-pullback`,
   `lem-weil-pbc-invertible-pullback-tensor`, and
   `lem-weil-pbc-invertible-pullback-invertible`. Apply
   `lem-sfb-norm-frame-tensor-section-gluing`: its norm module N has frames F_i
   with transitions norm(f^sharp a_ij) = a_ij^d. For the given section, written
   s = b_i E_i^n, it supplies a section t_N locally equal to norm(b_i) F_i^n.
2. Identify N.tensorPow n with L.tensorPow (d*n) by sending F_i^n to e_i^(d*n).
   Their transitions agree since (a_ij^d)^n = a_ij^(d*n). Tensor restrictions
   commute by `lem-weil-pbc-module-restriction-tensor-comparison`; tensor frames
   use the unitors and associators of `lem-weil-pbc-module-tensor-symmetric-monoidal`.
   Glue the local maps and their inverses by clause (1) of
   `lem-weil-pbc-glue-sheaves-of-modules`. The composites are identities locally,
   hence globally. Transport t_N to t, locally norm(b_i) e_i^(d*n).
3. In these frames, t is nonvanishing at x exactly when norm(b_i) is nonzero
   in the residue field at x. By `lem-sfb-finite-function-norm-nonvanishing`,
   this holds exactly when b_i is nonzero at every point over x: finiteness
   follows from finite local freeness, and the norm axioms hold by step 1.
   Since E_i^n is a frame, this is the fibre inclusion in the nonvanishing locus
   defined by `def-weil-pbc-ample-invertible-module`. The cover proves the equality.
4. Set-theoretically, the fibre over x is contained in Y_s precisely when no
   point of its complement maps to x, giving the complement-of-image equality.
-/
theorem exists_finiteLocallyFree_pullback_section_norm
    {X Y : Scheme.{u}} (f : Y ⟶ X) (d : ℕ) (hd : 1 ≤ d)
    [f.IsFiniteLocallyFreeOfDegree d] (L : X.Modules) [L.IsInvertible]
    (n : ℕ) (hn : 1 ≤ n) (s : Γ(((tensorPullback f).obj L).tensorPow n, ⊤)) :
    ∃ t : Γ(L.tensorPow (d * n), ⊤),
      nonvanishingLocus (L.tensorPow (d * n)) t =
          {x : X | f ⁻¹' {x} ⊆ nonvanishingLocus (((tensorPullback f).obj L).tensorPow n) s} ∧
        nonvanishingLocus (L.tensorPow (d * n)) t =
          (f '' (nonvanishingLocus (((tensorPullback f).obj L).tensorPow n) s)ᶜ)ᶜ := by
  sorry

end AlgebraicGeometry.Scheme.Modules
