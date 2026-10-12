/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.ULift
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
import Sheaf.Paper.GaloisLisseRepresentations

/-!
# A connected finite monodromy torsor trivializing a module sheaf

Source: Stacks Project, Tags 0DV5 (3), 0DV6 and the proof of 0A3R.
(blueprint: lem-weil-pbc-finite-monodromy-trivializing-torsor)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- A finite locally constant vector-space sheaf is constant on a connected finite
monodromy torsor. Source: Stacks Project, Tag 0DV5 (3), Tag 0DV6, and Tag 0A3R,
proof before the choice of a Sylow subgroup.
(blueprint: lem-weil-pbc-finite-monodromy-trivializing-torsor)

Proof:
1. Choose a point of the nonempty connected scheme U and an algebraic closure of
its residue field. The finite-module correspondence of 0DV5 (3) identifies G with
its finite-dimensional geometric stalk A and a continuous action of the fundamental
group. Since the coefficient field is finite, A is a finite set and its group of
linear automorphisms is finite.
2. Let Q be the image of this action. Replace Q by an isomorphic finite group in
Type u. The action factors through a continuous surjection onto Q, whose kernel
is open and normal. The Galois correspondence gives a connected finite etale
Q-torsor c over U. Transport its action along Q equiv ULift Q.
3. The fundamental group of the total space maps into the kernel. Pullback
compatibility (0DV6) makes the pulled-back representation trivial. The module
correspondence therefore identifies c*G with the constant sheaf with value A.
The stalk is finite-dimensional over ULift (ZMod l), giving the asserted instance.
For G = 0 use Q = 1, the identity torsor, and A = 0. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_monodromy_trivializing_torsor
    {U : Scheme.{u}} [ConnectedSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q)
      (c : Scheme.GaloisCover (ULift.{u + 1} Q) U) (_ : ConnectedSpace c.P)
      (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      (_ : FiniteDimensional (ULift.{u + 1} (ZMod ℓ)) A),
      Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G ≅
        (constantSheaf c.P.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A) := by sorry

end AlgebraicGeometry
