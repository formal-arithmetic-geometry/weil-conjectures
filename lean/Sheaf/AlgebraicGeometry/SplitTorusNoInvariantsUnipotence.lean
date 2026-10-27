/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket
public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy

/-! # A split torus action without invariant tangent vectors

Source: Milne, Algebraic Groups (2017), Propositions 16.62--16.63, p.347,
and Theorem 16.58, p.345
(blueprint: lem-sfb-split-torus-no-invariants-unipotence).

The fixed-vector condition uses every commutative algebra extension, including
nonreduced algebras. It is expressed on canonical dual-number tangent points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A split torus acting without invariant identity tangent vectors forces split
unipotence, with geometrically connected terms and represented additive quotients.
The Lie model here is canonically the scheme tangent space at the identity;
`GrpObj.tangentPoint` realizes each vector as its actual dual-number point.
Source: Milne, Propositions 16.62--16.63, p.347, and Theorem 16.58, p.345
(blueprint: lem-sfb-split-torus-no-invariants-unipotence).

Proof, following the five steps of the DAG node:
1. By lem-sfb-split-torus-representation-weight-decomposition the zero-character
   space is the fixed space. Choose an integer cocharacter avoiding the kernels
   of the finitely many nonzero weights (evaluate their nonzero integer polynomials
   at an integer avoiding all roots). The empty weight set permits the trivial
   cocharacter. Cotangent base change preserves the absence of invariants.
2. Over an algebraic closure form H semidirect S, with product
   (h,s)(h',s') = (h a(s,h'),ss'). It is smooth, connected, affine and finite type:
   use lem-pc-proper-base-change for smooth base change, lem-trf-smooth-composition,
   and lem-weil-pbc-geometrically-connected-product-components.
3. Choose a maximal torus containing S. By
   lem-sfb-normal-subgroup-maximal-torus-intersection its reduced identity-component
   intersection with H is a maximal torus of H. S fixes this torus, whose tangent
   space injects into Lie(H), so it is trivial. Use
   lem-sfb-borel-maximal-torus-conjugacy and
   lem-sfb-torus-free-implies-unipotent-arbitrary-field to obtain a faithful
   upper-unitriangular representation over k, giving the matrix assertion.
4. Apply lem-sfb-gm-action-attracting-subgroup-big-cell to the chosen cocharacter.
   Its positive and negative groups have strictly positive tangent weights after
   reversing the cocharacter on the negative group. By
   lem-sfb-positive-weight-affine-space-arbitrary-field each is an affine space.
   Their dense open product gives a dense affine-space chart in H. Restricting
   to the complement of the coordinate hyperplanes gives a dominant map from a
   split torus, including the rank-zero case.
5. By lem-sfb-smooth-unipotent-solvable, H is solvable over k. Apply
   lem-sfb-rosenlicht-split-solvable-criterion to this dominant map. Its unipotent
   clause supplies the required smooth geometrically connected closed subnormal
   series with represented G_a quotients. Step 3 supplies geometric matrix
   unipotence. For H = 1 the series has length zero; a faithful one-dimensional
   trivial representation suffices. No perfectness or characteristic restriction
   is used, and no infinitesimal character replaces an algebraic character. -/
theorem splitTorus_noInvariants_splitUnipotent
    (k : Type u) [Field k] (H S : Grp (Over (Spec (.of k))))
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [Smooth H.X.hom] [GeometricallyConnected H.X.hom]
    (r : ℕ) (hS : Nonempty (S ≅ MultiplicativeType.splitTorus k r))
    [ModObj S.X H.X] (hAut : TorusCharacterTangent.ActsByGroupAutomorphisms S H)
    (hInv : ∀ v : GrpObj.Lie H.X,
      (∀ (R : Type u) [CommRing R] [Algebra k R] (s : points S.X R),
        points.map S.X (TrivSqZeroExt.inlAlgHom k R R) s •
            points.map H.X
              (DualNumber.lift ⟨(Algebra.ofId k (DualNumber R), DualNumber.eps),
                DualNumber.eps_mul_eps, fun _ ↦ Commute.all _ _⟩)
              (GrpObj.tangentPoint v) =
          points.map H.X
            (DualNumber.lift ⟨(Algebra.ofId k (DualNumber R), DualNumber.eps),
              DualNumber.eps_mul_eps, fun _ ↦ Commute.all _ _⟩)
            (GrpObj.tangentPoint v)) → v = 0) :
    (∃ (m : ℕ) (U : Fin (m + 1) → Grp (Over (Spec (.of k)))),
      Nonempty (U 0 ≅ H) ∧ Nonempty (U (Fin.last m) ≅ Grp.trivial _) ∧
      (∀ a : Fin (m + 1), Smooth (U a).X.hom ∧ GeometricallyConnected (U a).X.hom) ∧
      ∀ a : Fin m, ∃ (i : U a.succ ⟶ U a.castSucc)
          (q : U a.castSucc ⟶ Grp.mk (StandardGroupSchemes.additive k)),
        IsClosedSubgroupScheme i.hom.hom ∧ IsNormalSubgroupScheme i.hom.hom ∧
          SolvableGroupStructure.IsFppfQuotient i.hom.hom q) ∧
      SolvableGroupStructure.IsUnipotent H := by
  sorry

end AlgebraicGeometry
