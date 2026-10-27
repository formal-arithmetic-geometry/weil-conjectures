/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.KrullDimension.Polynomial
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds

/-! # Straightening affine-line-generated subgroups of vector groups

Source: Conrad, The Structure of Solvable Groups over General Fields,
Proposition 1.15, printed p.9
(blueprint: lem-sfb-affine-line-generated-vector-subgroup-straightening).

The coordinate subgroup is specified on all test schemes: precisely the last
`N - d` coordinate morphisms vanish. Thus the conclusion is scheme-theoretic.
The automorphism is in the category of group schemes, without a linearity condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj MonObj

namespace AlgebraicGeometry

/-- The standard coordinate vector group, including the empty product.
This is just the categorical product of the already defined additive group.
Source: Conrad, Proposition 1.15, p.9
(blueprint: lem-sfb-affine-line-generated-vector-subgroup-straightening). -/
noncomputable abbrev affineLineVectorPower (k : Type u) [Field k] (n : ℕ) :
    Grp (Over (Spec (.of k))) :=
  ∏ᶜ fun _ : Fin n ↦ Grp.mk (StandardGroupSchemes.additive k)

/-- A smooth closed subgroup generated over a separable closure by pointed affine-line
maps can be straightened by a group-scheme automorphism to a coordinate direct factor.
Source: Conrad, Proposition 1.15, printed p.9
(blueprint: lem-sfb-affine-line-generated-vector-subgroup-straightening).

Proof:
1. Strongly induct on N. For N = 0 the subgroup is trivial. For N = 1, a proper
subgroup has a nonzero defining polynomial q. A nonconstant coordinate v(t) on a
curve would give deg(q(v)) = deg(q) deg(v), contradicting q(v) = 0. Pointedness
makes every constant curve zero. Minimality gives L_K = 0; faithful scalar extension
then gives L = 0. For L = E use the identity in every dimension.
2. For N > 1 and L proper, affine dimension drop and the polynomial dimension formula
(lem-wf-affine-dimension-drop, lem-sf-noetherian-polynomial-dimension) give dim L ≤ N-1.
3. If equality holds, lem-sfb-vector-hypersurface-additive-equation writes L as the
kernel of an additive homomorphism. Some generating curve is nonconstant. Apply
lem-sfb-additive-kernel-separable-axis-extraction to obtain a k-group automorphism
whose inverse image M of L contains the first coordinate axis A.
4. For either case project to V' = Ga^(N-1). Factor the projection through its fppf
image I by lem-sfb-algebraic-group-homomorphism-factorization; affineness supplies
separatedness (lem-weil-pbc-affine-source-morphism-separated). The affine normal
quotient theorem (lem-sfb-affine-normal-quotient-geometry) gives smoothness of I and
base change of the quotient. The projected curves generate I_K: pull back any closed
subgroup containing them, apply minimality, and use injectivity of the faithfully flat
coordinate map to detect equality of ideals. The image dimension bound
(lem-zl-finite-type-fibre-image-dimension-bounds) gives dim I ≤ dim M.
5. In codimension one, subtraction of the first coordinate gives M = A × M', where
M' = M ∩ (0 × V'). Its projection is M/A, hence smooth by the normal quotient theorem.
Its image is I since O(M') -> O(M')[t] is injective. Inductively straighten M' in V',
extend by the identity on A, compose with the previous automorphism and permute axes.
6. In higher codimension inductively straighten I in V' to Ga^e × 0. Then
 e = dim I ≤ dim L < N-1, so the transformed L lies in the smaller coordinate group
Ga^(e+1). Its curves still generate there. Induct in dimension e+1, extend this
automorphism by the identity on the remaining coordinates, and compose.
7. Restrict the resulting h to L and identify its coordinate image with Ga^d.
Conjugate the coordinate projection by this restriction and h to obtain r; on L
this is the identity. The cases d = 0, d = N and an empty family are included. -/
theorem affineLineGenerated_vectorSubgroup_straightening
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (N : ℕ) (L : Grp (Over (Spec (.of k))))
    [IsAffine L.X.left] [LocallyOfFiniteType L.X.hom] [QuasiCompact L.X.hom]
    [Smooth L.X.hom] (i : L ⟶ affineLineVectorPower k N)
    [IsClosedSubgroupScheme i.hom.hom]
    (K : Type u) [Field K] [Algebra k K] [IsSepClosure k K]
    (curves : Set (StandardGroupSchemes.additive K ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj L).X))
    (hpointed : ∀ f ∈ curves, (1 : StandardGroupSchemes.additive K ⟶
      StandardGroupSchemes.additive K) ≫ f = 1)
    (hgenerated : ∀ (J : Grp (Over (Spec (.of K))))
      (j : J.X ⟶ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj
          (affineLineVectorPower k N)).X), IsClosedSubgroupScheme j →
      (∀ f ∈ curves, ∃ g : StandardGroupSchemes.additive K ⟶ J.X,
        g ≫ j = f ≫ ((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.map i).hom.hom) →
      ∃ a : ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj L).X ⟶ J.X,
        a ≫ j = ((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.map i).hom.hom) :
    ∃ (h : affineLineVectorPower k N ≅ affineLineVectorPower k N) (d : ℕ),
      d ≤ N ∧
      (∀ (T : Over (Spec (.of k))) (x : T ⟶ (affineLineVectorPower k N).X),
        (∃ y : T ⟶ L.X, y ≫ i.hom.hom ≫ h.hom.hom.hom = x) ↔
          ∀ j : Fin N, d ≤ j.val →
            x ≫ (Pi.π (fun _ : Fin N ↦ Grp.mk (StandardGroupSchemes.additive k)) j).hom.hom
              = 1) ∧
      Nonempty (L ≅ affineLineVectorPower k d) ∧
      ∃ r : affineLineVectorPower k N ⟶ L, i ≫ r = 𝟙 L := by
  sorry

end AlgebraicGeometry
