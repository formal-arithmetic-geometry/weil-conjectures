/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Relative vanishing for the specified graph twist

Source: Stacks Project, Tags 02O5 and 02O1.
(blueprint: lem-pc-m1-projective-graph-twist-vanishing)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Relative Serre vanishing for the integral twist pulled back along a projective graph.

Source: Stacks Project, Tag 02O5, the graph construction of L, and Tag 02O1.
(blueprint: lem-pc-m1-projective-graph-twist-vanishing)

Proof: because g is separated, the lift of j to projective space over S is a closed
immersion. Compatibility with the integral projection identifies its pulled-back O(1)
with L. For nonempty finite N, reindex coordinates by ULift (Fin (m+1)); the standard
projective twisting sheaf is relatively ample. Hence L is ample on the inverse image
of each affine open of S. The structure module on Y is coherent, since p is finite
type over Noetherian S, and is quasi-coherent. Apply relative Serre vanishing (Tag 02O1)
to this structure module: affine-base vanishing gives a threshold on each member of a
finite affine cover of S; the maximum gives a common threshold for all positive
higher images. The unit tensor isomorphism identifies the resulting twists with
L.tensorPow. If N is empty, j forces Y empty; its module category is zero and one
may take threshold zero. -/
theorem exists_isZero_higherDirectImage_graph_twist
    {Y S T : Scheme.{u}} [IsNoetherian S]
    (g : S ⟶ T) [IsSeparated g] (p : Y ⟶ S) [IsProper p]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (hj : j ≫ (ℙ(N; T) ↘ T) = p ≫ g)
    [HasInjectiveResolutions Y.Modules] :
    let L := (pullback j).obj
      ((pullback (ProjectiveSpace.toProjInt N T)).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ q : ℕ, 0 < q →
      IsZero ((higherDirectImage p q).obj (L.tensorPow n)) := by sorry

end AlgebraicGeometry.Scheme.Modules
