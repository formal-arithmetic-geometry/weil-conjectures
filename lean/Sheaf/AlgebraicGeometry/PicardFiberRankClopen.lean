/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField

/-! # Clopen fibre-rank and empty-fibre loci

Source: Stacks Project, Tag 0BDP, first proof paragraph (rank decomposition).
(blueprint: lem-sc-picard-fiber-rank-clopen).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The empty-fibre locus and the locus of a prescribed constant fibre rank are clopen.
Empty fibres belong to every fixed-rank locus.
Source: Stacks Project, Tag 0BDP, first proof paragraph; the open-and-closed rank
argument applied without connectedness or surjectivity.
(blueprint: lem-sc-picard-fiber-rank-clopen).

Proof:
1. Finite local freeness gives a locally constant stalk-rank function on X. Its
   rank-r locus A and its complement B are both open and closed. Tensor pullback
   preserves stalk rank, so E on X_s has constant rank r iff X_s avoids B.
2. Flatness and local finite presentation make f an open map. Properness makes it
   a closed map. Thus f(A), f(B), and f(X) are all open and closed; the images of
   A and B may overlap, and no disjointness of their images is needed.
3. The fixed-rank locus is S minus f(B), and the empty-fibre locus is S minus f(X).
   These complements are clopen. For an empty fibre the rank condition is vacuous,
   which accounts for its inclusion even when r is positive. -/
theorem picardFiberRank_clopen {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    IsClopen {s : S | IsEmpty (pullback f (S.fromSpecResidueField s) : Scheme.{u})} ∧
      IsClopen {s : S | SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r} := by
  sorry

end AlgebraicGeometry.Scheme
