module

public import Sheaf.AlgebraicGeometry.WoundCckpKernel
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.FieldTheory.SeparableExtension
import Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.AlgebraicGeometry.Group.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.DensePoints

/-! # The canonical central p-torsion kernel and woundness

Source: Conrad, The structure of solvable groups over general fields (2014),
Definition 3.1 and the following paragraph, printed p.15, and Proposition 3.2 (1) and (3),
printed pp.15--16 (blueprint: lem-sfb-unipotent-cckp-kernel-wound-criterion).

Uniqueness is expressed by an isomorphism commuting with the closed inclusions.
Scalar extension uses the actual pullback functor, including on the inclusion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every smooth connected affine unipotent group in positive characteristic has a
unique largest smooth connected central closed subgroup killed by p. It is commutative,
commutes with separable scalar extension, and is wound exactly when the ambient group is.

Source: Conrad, Definition 3.1 and the paragraph following it, printed p.15;
Proposition 3.2 (1) iff (3), printed pp.15--16
(blueprint: lem-sfb-unipotent-cckp-kernel-wound-criterion).

Proof plan (the six steps of the DAG node):
1. Apply lem-sfb-affine-group-centre-base-change to Z(U). The p-fold power map is
   a homomorphism since Z(U) is commutative. By lem-sc-kernel-subgroup its kernel H
   is closed. Take J = H^natural from lem-sfb-separable-point-scheme-core. Its
   functoriality and product compatibility induce the group operations on J.
   By lem-sfb-geometrically-reduced-group-smooth, J is smooth, central and p-torsion.
2. Take F = J^0 using lem-sfb-finite-type-group-identity-subgroup. It is smooth,
   connected, central and killed by p. Every smooth connected central p-torsion
   subgroup B factors through H and, by sbc-lem-smooth-geometrically-reduced and core
   functoriality, through J. Its connected image containing the identity lies in J^0.
   This proves largestness. Mutual containment proves uniqueness as a closed subgroup.
   If U is trivial, H, J and F are all trivial.
3. The centre, p-fold power and kernel commute with scalar extension. The separable
   core commutes with separable extensions by lem-sfb-separable-point-scheme-core.
   By lem-sbc-connected-rational-point-geometrically-connected, the identity component
   F remains connected after extension, so F_K = (J_K)^0. Smoothness is stable under
   base change. The same connectedness lemma applies to U, and the closed embedding
   of lem-sfb-geometric-unipotence-unitriangular-embedding remains unipotent after
   base change. Thus the construction over K identifies the pulled-back F with its kernel.
4. If U is wound, compose any affine-line morphism into F with its inclusion in U.
   The composite is constant at its value at zero. Cancel the subgroup monomorphism
   to see that the original morphism is constant at its own rational value.
5. Conversely, translate a nonconstant affine-line curve in U to be pointed. Extend
   to a separable closure, where it remains nonconstant, and embed in a unitriangular
   group using lem-sfb-geometric-unipotence-unitriangular-embedding. If not central,
   replace a curve a by g^{-1}a^{-1}ga for an appropriate rational g. Smooth reducedness
   and lem-pc-rational-points-dense detect a nonzero commutator coefficient at such g.
   The filtration of lem-sfb-unitriangular-coordinate-filtration makes this operation
   move strictly deeper, so it eventually gives a central nonconstant pointed curve c.
6. Choose p^e at least the matrix size. The binomial identity for 1+N shows U is killed
   by p^e. Take the last nontrivial p-power of c. It is killed by p and factors through
   H, then J by the geometrically reduced affine line, then F by connectedness. Apply
   lem-sfb-commutative-p-torsion-vector-wound-factor to F. Its canonical vector factor
   must be nontrivial, since it contains this curve after separable extension. That
   lemma's criterion says F is not wound. This proves the converse by contrapositive.
   For the trivial U both wound conditions hold directly. -/
theorem exists_unipotent_cckpKernel_wound_criterion {k : Type u} [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (U : Grp (Over (Spec (.of k)))) (hU : SolvableGroupStructure.IsAlgebraic U)
    [Smooth U.X.hom] [ConnectedSpace U.X.left] (hunip : SolvableGroupStructure.IsUnipotent U) :
    ∃ (F : Grp (Over (Spec (.of k)))) (i : F ⟶ U),
      IsCckpKernel p i ∧ IsCommMonObj F.X ∧
      (∀ (F' : Grp (Over (Spec (.of k)))) (i' : F' ⟶ U),
        IsCckpKernel p i' → ∃ e : F ≅ F', e.hom ≫ i' = i) ∧
      (∀ (K : Type u) [Field K] [Algebra k K] (hK : Algebra.IsSeparableExtension k K),
        IsCckpKernel p ((MultiplicativeType.baseChange (K := K)).map i)) ∧
      (IsWound U ↔ IsWound F) := by
  sorry

end AlgebraicGeometry
