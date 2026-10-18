/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.SmoothTensorDuality
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift

/-! # Boundedness of the relative dual of a smooth lisse coefficient

Source: lem-asd-smooth-generic-direct-image, proof, finite-dimensional local calculation.
(blueprint: lem-asd-smooth-lisse-relative-dual-bounded).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The actual relative dual of a finite lisse prime-field sheaf is bounded constructible.
Source: blueprint lem-asd-smooth-generic-direct-image, first proof paragraph, construction of N
(blueprint: lem-asd-smooth-lisse-relative-dual-bounded).

Proof: The smooth relative dimension is locally constant. Quasi-compactness of X gives
finitely many clopen dimension pieces. On a piece of dimension d, smooth tensor duality
identifies the relative dualizing object with a rank-one finite lisse sheaf shifted by 2d.
Trivialize L and this sheaf on a common etale cover. Internal Hom from the finite free
coefficient module is a finite product of the identity, hence is exact, and its value on
the shifted line is its ordinary finite free dual tensored with that line, shifted by 2d.
Exact etale restriction and geometric-stalk conservativity identify these calculations
with the indicated derived internal Hom. Its only cohomology on each piece is finite
locally constant. Take common lower and upper bounds over the finitely many pieces;
their clopen stratifications give constructibility. For empty X all cohomology vanishes. -/
theorem isBoundedConstructible_smooth_lisse_relativeDual
    (ℓ : ℕ) [Fact ℓ.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    (hℓ : IsUnit (ℓ : Γ(S, ⊤)))
    (f : X ⟶ S) [IsSeparated f] [Smooth f]
    [LocallyOfFiniteType f] [QuasiCompact f] [HasCompactification f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) :
    DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) X
      ((verdierDual (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) f).obj
        (Opposite.op ((_root_.DerivedCategory.singleFunctor _ 0).obj L))) := by sorry

end AlgebraicGeometry.Etale
