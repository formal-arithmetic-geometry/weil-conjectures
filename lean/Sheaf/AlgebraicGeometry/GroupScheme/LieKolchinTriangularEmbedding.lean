module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Lie--Kolchin triangular embedding

Source: Milne, Algebraic Groups (2017), Theorem 16.30, printed pp.334--335,
and Proposition 16.2(a)--(c), printed pp.324--325.
(blueprint: lem-sfb-lie-kolchin-triangular-embedding)

A closed immersion into the upper triangular subgroup B_n is expressed as a closed
immersion into GL_n with all below-diagonal coordinates zero on every algebra of points.
Since B_n is the closed subscheme cut out by those coordinates, this is the same
scheme-theoretic conclusion. No restriction on the characteristic is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected solvable affine algebraic group over an algebraically closed field
has a closed embedding into the invertible upper triangular matrices of positive size.
Source: Milne, Algebraic Groups (2017), Theorem 16.30, pp.334--335, Proposition 16.2,
pp.324--325, and Theorem 4.9, p.87.
(blueprint: lem-sfb-lie-kolchin-triangular-embedding)

Proof:
1. The closed normal series gives a terminating abstract derived series of J(k):
   commutators in each term land in the next. Induct on this derived length to show
   that every nonzero simple rational representation of any smooth connected affine
   finite-type group H of that length has dimension one. A stable subspace of least
   positive dimension then gives a stable line in any nonzero representation.
   Smoothness implies reducedness (sbc-lem-smooth-geometrically-reduced).
   Matrix equations on H(k) are equations in k[H] by the vanishing principle
   (lem-wf-affine-nullstellensatz-vanishing). This also proves the length-zero case.
2. Take the smooth connected normal derived subgroup N with N(k)=[H(k),H(k)]
   (lem-sfb-smooth-connected-derived-subgroup). Restrict a simple representation V
   to N and apply induction to get a nonzero character eigenspace V_chi.
   Its nonzero character eigenspaces are independent and there are finitely many
   (lem-sfb-character-eigenspaces-independent), using the all-algebras eigenspaces.
3. Normality gives g V_chi = V_(chi^g), so H(k) permutes this finite set.
   The stabilizer of V_chi is cut out by lower-left matrix coefficients and is closed
   of finite index. Its cosets cover H: a nonempty open complement would contain
   a principal affine open and hence a k-point by the Nullstellensatz. Distinct cosets
   are disjoint as schemes' underlying closed sets, since a nonempty intersection
   would likewise have a k-point. Connectedness forces a single coset. Reducedness
   upgrades stability on k-points to group-scheme stability, so simplicity gives
   V=V_chi (the derived-subgroup, eigenspace, reducedness and vanishing nodes above).
4. For d=dim(V), N acts by scalar chi. Every n in N(k) is a product of commutators
   in H(k), so its representation determinant is one (def-sc-general-linear-group).
   Thus chi^d=1, first on points and then on k[N]. The fibres over the distinct roots
   of T^d-1 form a finite disjoint closed cover even when the polynomial has repeated
   roots. Connectedness leaves only the fibre containing the identity, namely chi=1.
   Reducedness and vanishing give chi-1=0. No reducedness of mu_d is needed.
5. Descend the representation through the fppf quotient H/N
   (lem-sfb-affine-normal-quotient-geometry): evaluate on local lifts, whose values
   agree because N acts trivially, then glue. The quotient is commutative because
   the commutator morphism factors through N. Its representation has a stable line
   (lem-sfb-commutative-group-representation-eigenline), so simplicity forces d=1.
   This completes the induction and the stable-line assertion for J.
6. Apply lem-sfb-normal-subgroup-representation-kernel to the trivial subgroup.
   Factor the resulting representation by lem-sfb-algebraic-group-homomorphism-factorization.
   The quotient by its trivial scheme-theoretic kernel is J, hence the representation
   is a closed immersion into GL_n, with n positive, not merely injective on k-points.
7. Induct on representation dimension: take a stable line and the rational quotient
   action, lift a full stable flag from the quotient, and choose an adapted basis.
   The zero-dimensional quotient uses the empty flag. For every algebra R the lower
   matrix entries vanish, so the representation factors through B_n. The surjection
   k[GL_n] -> k[J] kills those coordinates, hence induces a surjection k[B_n] -> k[J].
   Therefore J -> B_n is a closed immersion (def-weil-closed-immersion). -/
theorem lieKolchin_triangular_embedding {k : Type u} [Field k] [IsAlgClosed k]
    (J : Grp (Over (Spec (.of k)))) [IsAffine J.X.left]
    [LocallyOfFiniteType J.X.hom] [QuasiCompact J.X.hom]
    [Smooth J.X.hom] [ConnectedSpace J.X.left]
    (hsolv : SolvableGroupStructure.IsSolvable J) :
    ∃ (n : ℕ), 0 < n ∧
      ∃ r : J.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
        IsClosedSubgroupScheme r ∧
        ∀ (R : Type u) [CommRing R] [Algebra k R]
          (x : (Spec (.of R)).asOver (Spec (.of k)) ⟶ J.X) (i j : Fin n),
          j < i →
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
              ⟨i⟩ ⟨j⟩ = 0 := by
  sorry

end AlgebraicGeometry
