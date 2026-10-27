/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.CompleteFlagPoints
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.FreeQuotientGrassmannProjective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates

/-! # Realizing solvable subgroups as complete-flag stabilizers

Source: Milne, Algebraic Groups (2017), Theorems 4.9, 4.27, 16.30 and 17.9;
Propositions 7.29--7.30 and Section 1, Corollary 1.39.
(blueprint: lem-sfb-solvable-subgroup-flag-realization)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected solvable closed subgroup is a complete-flag stabilizer in a
faithful representation. The affine-point classification of the projective flag scheme
is natural under every algebra map. Every faithful flag stabilizer has a smooth connected
solvable reduced identity subgroup of the same topological Krull dimension.

Source: Milne, 4.9, p.87; 4.27, pp.94--95; 16.30, pp.334--335; 17.9, p.354;
7.29--7.30, pp.146--147; 1.34--1.39, pp.16--19; Section 16a.
(blueprint: lem-sfb-solvable-subgroup-flag-realization)

Proof:
1. Chevalley's line-stabilizer theorem gives a representation E and a line L with
   stabilizer H on every algebra. The prescribed-kernel representation theorem for
   the trivial subgroup and homomorphism factorization give a closed faithful W.
2. Replace E by E ⊕ W. The block-diagonal graph is closed, so the sum is faithful,
   and the stabilizer of L ⊕ 0 remains exactly H. This space is nonzero.
3. Construct an H-stable complete flag in V/L by induction on dimension. The
   Grassmannian of lines is projective and nonempty, so the Borel fixed-point
   theorem gives an H-stable line. Continue on its quotient. Pulling the flag back
   to V gives first term L. Its stabilizer is H on every algebra by step 1.
4. In the product of quotient Grassmannians impose the incidence equations
   S_i → V → Q_(i+1) = 0. Their matrix-entry ideals glue and represent nested
   locally direct summands on arbitrary test algebras. Their successive quotients
   are locally free. The construction commutes with every scalar extension.
5. Plücker embeddings and the Segre embedding make this incidence scheme projective.
   For dimension one use Spec k = P⁰. Closed reduced subschemes remain projective,
   hence proper and of finite type.
6. For any faithful representation and flag, choose an adapted basis. Its stabilizer
   is the inverse image of the upper triangular group, hence affine closed of finite
   type. Its reduced identity component is smooth and connected over the perfect
   field k. Reduction commutes with the open identity component, so this is also
   the identity component of the reduction. Dimension zero representations force
   G to be trivial and satisfy the same assertions.
7. The diagonal quotient of this smooth connected triangular subgroup is commutative
   with smooth unipotent kernel. A terminating commutative normal series for that
   kernel, preceded by the diagonal quotient, forces termination of the derived
   series, since each commutator subgroup lies in the next term.
8. Translations identify the finitely many components of the stabilizer with its
   identity component. An irreducible chain lies in one clopen component, so all
   components have the same dimension. Reduction preserves the underlying space,
   proving the equality of topological Krull dimensions. -/
theorem solvableSubgroup_flag_realization
    {k : Type u} [Field k] [IsAlgClosed k]
    (G H : Over (Spec (.of k))) [GrpObj G] [GrpObj H]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsAffine H.left] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    [Smooth G.hom] [ConnectedSpace G.left] [Smooth H.hom] [ConnectedSpace H.left]
    (i : H ⟶ G) [IsClosedSubgroupScheme i] (hsolv : IsSolvableGroupScheme H) :
    (∃ (n : ℕ) (r : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} n) k)
        (L : CompleteFlagPoints.Points n k),
      0 < n ∧ IsMonHom r ∧ IsClosedImmersion r.left ∧
        CompleteFlagPoints.IsStabilizer i r L ∧
      ∃ (X : Over (Spec (.of k)))
        (e : ∀ (A : Type u) [CommRing A] [Algebra k A],
          ((Spec (.of A)).asOver (Spec (.of k)) ⟶ X) ≃ CompleteFlagPoints.Points n A),
        IsProjective X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
        (∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
          (f : A →ₐ[k] B) (x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ X),
          (e B ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of k)) ≫ x)).val =
            CompleteFlagPoints.extend f.toRingHom (e A x).val) ∧
        ∀ (Z : Over (Spec (.of k))) (j : Z ⟶ X),
          IsClosedImmersion j.left → IsReduced Z.left →
            IsProper Z.hom ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom) ∧
    (∀ (m : ℕ) (s : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} m) k)
        (E : CompleteFlagPoints.Points m k),
      IsMonHom s → IsClosedImmersion s.left →
      ∃ (K : Over (Spec (.of k))) (_ : GrpObj K) (j : K ⟶ G),
        IsClosedSubgroupScheme j ∧ CompleteFlagPoints.IsStabilizer j s E ∧
      ∃ U : K.left.Opens,
        (U : Set K.left) = connectedComponent (GrpObj.onePoint K) ∧
      ∃ gJ : GrpObj (Over.mk (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ K.hom)),
        IsClosedSubgroupScheme
          (Over.homMk
            (U := Over.mk (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ K.hom))
            (V := K) (U.toScheme.nilradical.subschemeι ≫ U.ι)) ∧
        Smooth (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ K.hom) ∧
        ConnectedSpace U.toScheme.nilradical.subscheme ∧
        @IsSolvableGroupScheme k _
          (Over.mk (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ K.hom)) gJ ∧
        topologicalKrullDim U.toScheme.nilradical.subscheme = topologicalKrullDim K.left) := by
  sorry

end AlgebraicGeometry
