/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
import WeilConjectures.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import Sheaf.AlgebraicGeometry.RegularClosedPointComponents
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Dimensions of the kernel and closed image of a group homomorphism

Source: Milne, Algebraic Groups (2017), Proposition 5.23, printed p.104;
Theorem 5.39 and Remark 5.42, printed pp.108--109; Corollary 1.35, printed p.17.
(blueprint: lem-sfb-group-hom-dimension-kernel-image)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The dimension formula for the closed image and scheme-theoretic kernel of a homomorphism
of affine finite-type group schemes. For a smooth connected target, the analogous equality
with the target dimension characterizes faithful flatness. All four dimensions are finite
nonnegative integers. The factorization is supplied by
`algebraicGroup_homomorphism_factorization`; `GrpObj.ker` is the pullback along the unit.

Source: Milne, Algebraic Groups (2017), Proposition 5.23, printed p.104, and
Theorem 5.39 and Remark 5.42, printed pp.108--109, with Corollary 1.35, printed p.17.
(blueprint: lem-sfb-group-hom-dimension-kernel-image)

Proof plan, following the six steps of the DAG node:
1. Affine schemes are separated (lem-weil-pbc-affine-source-morphism-separated).
   The homomorphism factorization supplies a finite-type image and kernel and a flat,
   finitely presented quotient (lem-sfb-algebraic-group-homomorphism-factorization).
   Each group has an identity point, so its dimension is nonnegative; finite type over
   a field makes it finite (lem-kun-dimension-finite-type). The dimensions of
   def-kun-dimension and def-kun-topological-krull-dimension both count the same chains.
2. Apply lem-sbc-flat-composite-fibre-dimension-at-point to q and I -> Spec k at the
   identity. Its fibre is the kernel, since j is a closed immersion. The identity points
   are rational; lem-ag-rational-point-stalk-topological-local-dimension converts their
   point dimensions to stalk dimensions, and lem-ag-group-identity-local-dimension
   converts these to global dimensions. This gives dim G = dim L + dim I.
3. If H is smooth and connected, sbc-lem-smooth-geometrically-reduced makes H reduced
   (apply it to the trivial separably closed extension k/k). Its local rings are regular
   by the affine smooth-ring description and lem-weil-pbc-smooth-over-field-regular-local.
   Then lem-wf-smooth-components-disjoint makes H irreducible, and
   lem-wf-affine-dimension-drop makes its coordinate algebra A a domain.
4. Write the closed immersion as Spec(A/J) -> Spec A. A nonzero J misses the generic
   point, so its closed subset is proper. By lem-weil-pbc-spec-topological-krull-dimension-ring
   and lem-wf-affine-dimension-drop it has strictly smaller dimension. Nilpotents do not
   change dimension. Thus dim I = dim H holds exactly when J = 0.
5. Faithful flatness of f implies surjectivity of j, which forces J = 0 in the domain A.
   Conversely, J = 0 makes j an isomorphism, so f is flat and surjective because q is
   (def-weil-flat-morphism, def-weil-closed-immersion and the factorization theorem).
6. Cancel the finite nonnegative dimension of L in step 2 to obtain the criterion.
   No smoothness or connectedness of G or L, or separability of f, is used. -/
theorem algebraicGroup_hom_dimension_kernel_image
    {k : Type u} [Field k] [IsAlgClosed k]
    (G H I : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [IsAffine H.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (f : G ⟶ H) (q : G ⟶ I) (j : I ⟶ H) (hfactor : q ≫ j = f)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    [QuasiSeparated q.hom.hom.left] [IsClosedImmersion j.hom.hom.left] :
    (∃ dG dH dI dL : ℕ,
      topologicalKrullDim G.X.left = (dG : WithBot ℕ∞) ∧
      topologicalKrullDim H.X.left = (dH : WithBot ℕ∞) ∧
      topologicalKrullDim I.X.left = (dI : WithBot ℕ∞) ∧
      topologicalKrullDim (GrpObj.ker f.hom.hom).left = (dL : WithBot ℕ∞)) ∧
    topologicalKrullDim G.X.left =
      topologicalKrullDim I.X.left + topologicalKrullDim (GrpObj.ker f.hom.hom).left ∧
    (Smooth H.X.hom → ConnectedSpace H.X.left →
      ((Flat f.hom.hom.left ∧ Surjective f.hom.hom.left) ↔
        topologicalKrullDim G.X.left =
          topologicalKrullDim H.X.left + topologicalKrullDim (GrpObj.ker f.hom.hom).left)) := by
  sorry

end AlgebraicGeometry
