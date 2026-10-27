/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.AlgebraicGeometry.RelativeSplitTorus
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import Sheaf.AlgebraicGeometry.ProjectiveClosedSubschemeHomogeneousIdeal
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Invariant affine charts for relative split-torus actions

Source: Thomason, Equivariant resolution, linearization, and Hilbert's fourteenth
problem over arbitrary base schemes, Adv. Math. 65 (1987), Theorem 3.3 and
Corollary 3.4(3), printed p.32, followed by boundary-avoiding weight charts.
(blueprint: lem-sfb-relative-split-torus-invariant-affines).

An action object contains the action morphism over S and its unit and associativity
identities. An open immersion of action objects records the restricted action and
its equivariance, hence scheme-theoretic invariance of the affine open.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every point has a split-torus-invariant affine open neighbourhood; these opens cover X.
Source: Thomason (1987), Theorem 3.3 and Corollary 3.4(3), printed p.32,
with the boundary-avoiding weight-chart argument of the node.
(blueprint: lem-sfb-relative-split-torus-invariant-affines).

Proof:
1. Write S = Spec A. By pqf-lem-affine-open-locnoeth, A is Noetherian.
   Apply lem-weil-pbc-ample-very-ample-immersion-affine-base to the ample L.
   Then lem-sfb-relative-torus-diagonal-projective-embedding gives an equivariant
   immersion j into a finite projective space with diagonal coordinate weights.
   Normal local domains imply reducedness. The empty X case is vacuous.
2. Apply lem-sfb-relative-diagonal-projective-boundary to the reduced locally closed
   image W. It gives invariant reduced closed Z and B, W = Z minus B, and stable
   modules of homogeneous boundary equations. By
   lem-sfb-projective-closed-subscheme-homogeneous-ideal, these equations define B
   as Proj of the graded quotient, over A and not merely on rational points.
3. At j(x), choose a homogeneous boundary equation outside the corresponding prime
   (def-pc-proj). If its degree is zero, multiply by a coordinate outside the prime.
   Decompose into its finitely many weight components; stability keeps them in the
   boundary ideal, and some component h is outside the prime. Its degree is positive.
4. Set U = j inverse D_+(h). This contains x and equals Z intersect D_+(h), because
   h vanishes on B. By prop-nagata-proj-standard-open, D_+(h) is affine. By
   def-weil-closed-immersion its closed subscheme Z intersect D_+(h) is affine too.
5. On every test A-algebra, h(t v) = t^m h(v), where t^m is a unit. Thus D_+(h)
   is invariant, including on nonreduced test algebras. Apply this to the universal
   point of T ×_S U. Equivariance of j and def-weil-open-immersion factor the action
   through U. Cancel its monic inclusion to obtain the action identities. The resulting
   equivariant open immersions cover X since x was arbitrary. For rank zero the sole
   weight is zero and the same argument applies. -/
theorem exists_relative_split_torus_invariant_affine_neighbourhood
    (S : Scheme.{u}) [IsAffine S] [IsLocallyNoetherian S] (r : ℕ)
    (X : CategoryTheory.Mod (Over S) (relativeSplitTorus S r).X)
    [IsSeparated X.X.hom] [LocallyOfFiniteType X.X.hom] [QuasiCompact X.X.hom]
    (hnormal : ∀ p : X.X.left,
      IsDomain (X.X.left.presheaf.stalk p) ∧
        IsIntegrallyClosed (X.X.left.presheaf.stalk p))
    (L : X.X.left.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple X.X.left L)
    (x : X.X.left) :
    ∃ (U : CategoryTheory.Mod (Over S) (relativeSplitTorus S r).X) (i : U ⟶ X),
      IsOpenImmersion i.hom.left ∧ IsAffine U.X.left ∧ x ∈ Set.range i.hom.left := by
  sorry

end AlgebraicGeometry
