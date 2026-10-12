/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Exact.Basic
import Sheaf.RingTheory.DepthExt

/-!
# Depth in a short exact sequence

Source: Stacks Project, Algebra, Lemma Tag 00LX (blueprint: lem-weil-pbc-depth-in-ses).
-/

@[expose] public section

universe u v₁ v₂ v₃

namespace IsLocalRing

/-- Stacks Project, Algebra, Lemma Tag 00LX (blueprint: lem-weil-pbc-depth-in-ses).
The depth inequalities for a short exact sequence of nonzero finite modules over a
Noetherian local ring, proved as follows.

1. By Tag 00LW (lem-weil-pbc-depth-ext), each depth is the least degree of a nonzero
   Ext group from the residue field. Thus depth at least n is equivalent to Ext
   vanishing in every degree i with 0 ≤ i < n.
2. Tag 00LU (lem-weil-pbc-ext-long-exact-second-variable) gives the three consecutive
   pieces of the long exact Ext sequence, and injectivity of Hom into the middle
   term. In an exact triple, zero outer terms force the middle term to be zero.
3. For n = min(depth N', depth N''), both outer Ext groups vanish for i < n.
   Exactness forces Ext of N to vanish in those degrees, proving (1).
4. For n = min(depth N, depth N' - 1), Ext of N in degree i and of N' in degree
   i + 1 vanish when 0 ≤ i < n. Exactness gives vanishing of Ext of N'', proving
   (2). When depth N' = 0, the inequality is automatic by nonnegativity; truncated
   subtraction on extended naturals expresses the same bound.
5. For n = min(depth N, depth N'' + 1), Ext of N vanishes for i < n. In degree
   zero, injectivity gives vanishing for N'. In degree i ≥ 1, Ext of N'' in degree
   i - 1 also vanishes, so exactness gives vanishing for N', proving (3). -/
theorem depth_in_short_exact
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N' : Type v₁} [AddCommGroup N'] [Module R N'] [Module.Finite R N'] [Nontrivial N']
    {N : Type v₂} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    {N'' : Type v₃} [AddCommGroup N''] [Module R N''] [Module.Finite R N''] [Nontrivial N'']
    (f : N' →ₗ[R] N) (g : N →ₗ[R] N'')
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    depth (R := R) N ≥ min (depth (R := R) N') (depth (R := R) N'') ∧
      depth (R := R) N'' ≥ min (depth (R := R) N) (depth (R := R) N' - 1) ∧
      depth (R := R) N' ≥ min (depth (R := R) N) (depth (R := R) N'' + 1) := by
  sorry

end IsLocalRing
