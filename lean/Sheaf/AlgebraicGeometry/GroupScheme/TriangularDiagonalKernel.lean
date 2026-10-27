module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Mathlib.RingTheory.FinitePresentation

/-!
# The diagonal kernel of a triangular group scheme

Source: Milne, Algebraic Groups (2017), Proposition 16.2, Theorem 16.26(a),
Note 16.10 and Corollary 14.12
(blueprint: lem-sfb-triangular-diagonal-kernel).

A closed subgroup of B_n is expressed by its closed embedding in GL_n and the
upper triangular equations on all algebra-valued points. Its intersection with
U_n is the diagonal-one subfunctor, specified by the kernel square and the
pointwise equivalence below. This includes nonreduced test algebras and groups.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The diagonal kernel, represented fppf quotient, and algebraically closed splitting
of a triangular group scheme. The matrix equations express the closed subgroup
V of U_n without imposing smoothness on V. The product is an isomorphism of
schemes over k; it is not asserted to be a direct product of groups.

Source: Milne, Proposition 16.2(c) implies (d), p.325, Theorem 16.26(a), pp.332--333,
and Note 16.10, p.326 (blueprint: lem-sfb-triangular-diagonal-kernel).

Proof plan:
1. On every algebra, diagonal entries multiply and invert componentwise. These
coordinate functions define delta. Its scheme kernel (lem-sc-kernel-subgroup)
is exactly the diagonal-one subfunctor J intersect U_n. Conjugation preserves
that subfunctor, and its defining equations give a closed embedding into U_n.
2. Apply lem-sfb-algebraic-group-homomorphism-factorization to delta. Its image
D is the represented fppf quotient by V and embeds closed in the split torus.
Over an algebraically closed field, lem-sfb-split-torus-subgroups-diagonalizable
makes D diagonalizable, including nonreduced D.
3. Intersect J with lem-sfb-unitriangular-coordinate-filtration. The successive
kernels give a finite J-normal filtration of V. By the homomorphism theorem its
successive quotients embed in Ga, equivariantly for the diagonal ratio character.
4. Induct on this filtration. Quotient by its last term using
lem-sfb-affine-normal-quotient-geometry and split the shorter extension. Pull
back along that section. The remaining additive-subgroup extension splits by
lem-sfb-additive-subgroup-diagonalizable-extension-splitting; composing its
section with the pullback projection splits J -> D, as in Milne's diagram (118).
5. Multiplication (v,d) -> v s(d) has inverse
j -> (j s(q(j))^(-1), q(j)); its first component factors through the kernel.
These are scheme morphisms and their two composites are identities.
6. If J is smooth and connected, the product gives scheme retractions onto V
and D. Lift maps from affine first-order thickenings into J and retract, proving
formal smoothness of both. Their affine finite-type algebras are finitely
presented over the field (lem-pc-affine-finite-type-algebra and
lem-weil-pbc-finite-type-noetherian-finite-presentation), so both are smooth.
Surjective retractions of a connected space are connected. -/
theorem triangular_diagonal_kernel {k : Type u} [Field k]
    (n : ℕ) (hn : 0 < n) (J : Grp (Over (Spec (.of k))))
    [IsAffine J.X.left] [LocallyOfFiniteType J.X.hom] [QuasiCompact J.X.hom]
    (r : J.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k)
    [IsClosedSubgroupScheme r]
    (hupper : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ J.X)
      (i j : Fin n), j < i →
      (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ r)).val ⟨i⟩ ⟨j⟩ = 0) :
    ∃ (δ : J ⟶ ∏ᶜ (fun _ : Fin n ↦ Grp.mk (StandardGroupSchemes.multiplicative k)))
      (V : Grp (Over (Spec (.of k)))) (iV : V ⟶ J)
      (D : Grp (Over (Spec (.of k)))) (q : J ⟶ D)
      (d : D ⟶ ∏ᶜ (fun _ : Fin n ↦ Grp.mk (StandardGroupSchemes.multiplicative k))),
      (∀ (A : Type u) [CommRing A] [Algebra k A]
        (x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ J.X) (i : Fin n),
        (WithConv.ofConv (Spec.mapMulEquiv.symm
          (x ≫ δ.hom.hom ≫ (Pi.π
            (fun _ : Fin n ↦ Grp.mk (StandardGroupSchemes.multiplicative k)) i).hom.hom)))
          (LaurentPolynomial.T 1) =
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ r)).val ⟨i⟩ ⟨i⟩) ∧
      IsClosedSubgroupScheme iV.hom.hom ∧ IsNormalSubgroupScheme iV.hom.hom ∧
      IsAffine V.X.left ∧ LocallyOfFiniteType V.X.hom ∧ QuasiCompact V.X.hom ∧
      IsPullback iV.hom.hom (toUnit V.X) δ.hom.hom
        η[(∏ᶜ (fun _ : Fin n ↦ Grp.mk (StandardGroupSchemes.multiplicative k))).X] ∧
      (∀ (A : Type u) [CommRing A] [Algebra k A]
        (x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ J.X),
        (∃ v : (Spec (.of A)).asOver (Spec (.of k)) ⟶ V.X, v ≫ iV.hom.hom = x) ↔
          ∀ i : Fin n,
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ r)).val ⟨i⟩ ⟨i⟩ = 1) ∧
      IsClosedSubgroupScheme (iV.hom.hom ≫ r) ∧
      (∀ (A : Type u) [CommRing A] [Algebra k A]
        (v : (Spec (.of A)).asOver (Spec (.of k)) ⟶ V.X),
        (∀ i : Fin n,
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A
            (v ≫ iV.hom.hom ≫ r)).val ⟨i⟩ ⟨i⟩ = 1) ∧
        (∀ i j : Fin n, j < i →
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A
            (v ≫ iV.hom.hom ≫ r)).val ⟨i⟩ ⟨j⟩ = 0)) ∧
      IsAffine D.X.left ∧ LocallyOfFiniteType D.X.hom ∧ QuasiCompact D.X.hom ∧
      IsFppfGroupQuotient iV q ∧ q ≫ d = δ ∧ IsClosedSubgroupScheme d.hom.hom ∧
      (IsAlgClosed k → ∃ s : D ⟶ J, s ≫ q = 𝟙 D ∧
        IsIso (lift (fst V.X D.X ≫ iV.hom.hom) (snd V.X D.X ≫ s.hom.hom) ≫ μ[J.X]) ∧
        (Smooth J.X.hom → ConnectedSpace J.X.left →
          Smooth V.X.hom ∧ ConnectedSpace V.X.left ∧
          Smooth D.X.hom ∧ ConnectedSpace D.X.left)) := by
  sorry

/-- For smooth affine finite-type groups, scheme-theoretic unitriangular
unipotence agrees with geometric matrix unipotence in a faithful representation.
Source: Milne, Corollary 14.12 and Theorem 14.5, pp.281--283
(blueprint: lem-sfb-triangular-diagonal-kernel).

Proof plan (step 7 of the node): apply
lem-sfb-geometric-unipotence-unitriangular-embedding to the faithful representation
in the geometric-point condition. Conversely the unitriangular embedding is a
faithful representation, and (u-I)^n=0: each entry is a sum over strictly
increasing chains of n+1 indices in n positions, so all summands vanish.
The smoothness hypothesis is retained in both directions. -/
theorem smooth_unitriangular_iff_geometric_unipotent {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] :
    (∃ n : ℕ, 0 < n ∧
      ∃ r : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
        IsClosedSubgroupScheme r ∧
        ∀ (A : Type u) [CommRing A] [Algebra k A]
          (x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.X),
          (∀ i : Fin n,
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ r)).val
              ⟨i⟩ ⟨i⟩ = 1) ∧
          (∀ i j : Fin n, j < i →
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ r)).val
              ⟨i⟩ ⟨j⟩ = 0)) ↔ SolvableGroupStructure.IsUnipotent G := by
  sorry

end AlgebraicGeometry
