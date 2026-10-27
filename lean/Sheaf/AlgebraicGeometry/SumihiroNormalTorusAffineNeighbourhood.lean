/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.AlgebraicGeometry.ProjectiveClosedSubschemeHomogeneousIdeal
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Invariant affine neighbourhoods for normal schemes with a split torus action

Source: Sumihiro, Equivariant completion (1974), Corollary 2 (WANTED in the DAG).
This is a supporting input to the concentration prerequisite of Milne,
Algebraic Groups (2017), Section 22d, Theorem 22.50, p.480; it is not attributed to Milne.
(blueprint: lem-sfb-sumihiro-normal-torus-affine-neighbourhood).

An action is an internal module object in schemes over Spec F. A morphism of these
objects is equivariant as a scheme morphism. Normality is stated on every local ring.
An equivariant open immersion from an affine scheme gives the required invariant
affine open subscheme, with its restricted action.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every point of a normal separated finite-type scheme with a split torus action
has an invariant affine open neighbourhood, with an action making its inclusion equivariant.

Source: Sumihiro, Equivariant completion (1974), Corollary 2 (WANTED in the DAG),
in the normal scheme form specified in the node; supporting input to Milne (2017),
Section 22d, Theorem 22.50, p.480.
(blueprint: lem-sfb-sumihiro-normal-torus-affine-neighbourhood).

Proof, following the accepted six-step split:
1. The empty scheme has no points. For a point x, the Laurent torus is smooth,
   nonempty and connected by lem-trf-split-lattice-torus-projection: its coordinate
   ring is a domain. Apply lem-sfb-sumihiro-invariant-quasiprojective-open to obtain
   an invariant normal quasi-projective open W containing x. This includes rank zero.
2. Apply lem-sfb-normal-quasiprojective-equivariant-immersion to embed W equivariantly
   in the projective space of a nonzero finite-dimensional representation. Normality
   implies reducedness. By lem-sfb-projective-invariant-boundary-ideals, its reduced
   closure Z and reduced boundary B are invariant, W = Z minus B as open schemes,
   and every degree piece I(B)_d is a finite-dimensional torus subrepresentation.
3. By lem-sfb-projective-closed-subscheme-homogeneous-ideal, I(B) realizes B as a
   projective closed subscheme. The prime representing j(x) does not contain I(B).
   Choose a homogeneous f in I(B) outside that prime. If its degree is zero,
   multiply by a coordinate outside the prime to obtain positive degree. This also
   handles empty B and uses no rational-point or closed-point assumption on x.
4. By lem-sfb-split-torus-representation-weight-decomposition, decompose f inside
   I(B)_d into weight components. Some component h remains outside the prime.
   It vanishes on the whole boundary and has the same positive degree.
5. Put U = j inverse D_+(h). It contains x and, because h vanishes on B, identifies
   with Z intersect D_+(h). By prop-nagata-proj-standard-open the chart is affine;
   its closed subscheme Z intersect D_+(h) is affine by def-weil-closed-immersion.
   Thus U is an affine open of W and X, rather than just a locally closed affine chart.
6. On every test algebra, h(rho(g)v) = chi(g) inverse times h(v), using the
   contragredient polynomial action. The multiplier is a unit, so D_+(h) is invariant,
   also on nonreduced test algebras. Equivariance of j and def-weil-open-immersion
   factor the action through U. Cancel the monic open inclusion to check its identity
   and associativity laws; the factorization itself is equivariance. Rank zero,
   ineffective actions and arbitrary characteristic satisfy the same argument. -/
theorem exists_sumihiro_normal_torus_affine_neighbourhood
    (F : Type u) [Field F] [IsAlgClosed F] (r : ℕ)
    (T : Grp (Over (Spec (.of F))))
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (X : CategoryTheory.Mod (Over (Spec (.of F))) T.X)
    [IsSeparated X.X.hom] [LocallyOfFiniteType X.X.hom] [QuasiCompact X.X.hom]
    (hnormal : ∀ p : X.X.left,
      IsDomain (X.X.left.presheaf.stalk p) ∧
        IsIntegrallyClosed (X.X.left.presheaf.stalk p))
    (x : X.X.left) :
    ∃ (U : CategoryTheory.Mod (Over (Spec (.of F))) T.X) (i : U ⟶ X),
      IsOpenImmersion i.hom.left ∧ IsAffine U.X.left ∧ x ∈ Set.range i.hom.left := by
  sorry

end AlgebraicGeometry
