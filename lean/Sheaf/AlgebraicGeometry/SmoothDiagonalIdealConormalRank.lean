/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.DiagonalConormalDifferentials

/-! # The ideal-sheaf conormal and its rank for a smooth closed diagonal

Source: Stacks Project, Tags 08S2 and 02G1
(blueprint: lem-sc-smooth-diagonal-ideal-conormal-rank).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The conormal used by Koszul duality agrees with relative differentials and has
stalk rank equal to the pure relative dimension. This concerns only module sheaves,
without derived categories or a duality adjunction.
Source: Stacks Project, Tags 08S2 and 02G1
(blueprint: lem-sc-smooth-diagonal-ideal-conormal-rank).

Proof: write i for the closed diagonal. The canonical isomorphism from X to the
closed subscheme defined by i.ker commutes with the maps to the fibre product.
Its pushforward identifies the two maps from the structure sheaf, hence their
kernels: i.ker.toModules is isomorphic to the module-sheaf kernel defining
 diagonalConormal. Tensor pullback carries this isomorphism to X. Compose with
 diagonalConormal_iso_relativeDifferentials. The theorem
 isFiniteLocallyFreeOfRank_relativeDifferentials gives local trivializations by
O_X^d. Taking stalks gives free modules O_{X,x}^d, whose finrank is d because
these local rings are nontrivial. Transport finrank along the stalk isomorphism.
For empty X the stalk assertion is vacuous; for d = 0 the free module is zero. -/
theorem smoothDiagonal_idealConormal_iso_and_rank {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f]
    [IsClosedImmersion (pullback.diagonal f)] :
    Nonempty (((Scheme.Modules.tensorPullback (pullback.diagonal f)).obj
      (pullback.diagonal f).ker.toModules) ≅ f.relativeDifferentials) ∧
    ∀ x : X, Module.finrank (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        ((Scheme.Modules.tensorPullback (pullback.diagonal f)).obj
          (pullback.diagonal f).ker.toModules)) = d := by sorry

end AlgebraicGeometry
