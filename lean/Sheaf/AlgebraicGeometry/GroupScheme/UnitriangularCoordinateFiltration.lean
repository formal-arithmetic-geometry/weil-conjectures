module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Flat.Basic

/-! # The coordinate central filtration of the unitriangular group

Source: Milne, Algebraic Groups (2017), Example 6.49(a)--(c), pp.136--137,
and Theorem 16.21, p.330 (blueprint: lem-sfb-unitriangular-coordinate-filtration).

The existentially presented closed subgroups are specified on every algebra, including
nonreduced algebras, so their scheme structures are retained. The bijection C uses zero-based
indices: C r is the paper's C_(r+1), and H r is U^(r). The family delta gives the components
of the diagonal homomorphism into the product of n copies of the multiplicative group.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- The height-then-row coordinate filtration, including its canonical additive projections,
scheme-theoretic kernels, fppf quotient presentations, and diagonal conjugation characters.

Source: Milne, Algebraic Groups (2017), Example 6.49(a)--(c), pp.136--137,
and Theorem 16.21, p.330 (blueprint: lem-sfb-unitriangular-coordinate-filtration).

Proof plan (the seven steps of the DAG node):
1. Triangular determinant expansion gives k[B]=k[d_i^±1,x_l]; imposing diagonal ones and
   the first r zero coordinates gives k[H r]=k[x_(r+1),...,x_m]. The quotient maps give
   closed immersions, and these presentations give finite type. Use def-sc-general-linear-group,
   def-weil-affine-spectrum, def-weil-pbc-mv-polynomial-ring and def-weil-closed-immersion.
2. Strictly upper triangular N has N^n=0, by its increasing-chain entry formula. Thus
   (I+N)^-1=I-N+...+(-N)^(n-1). In any killed entry all product cross terms involve a
   smaller-height coordinate, so the displayed equations define subgroups. The first
   term is U_n and the last is the identity (def-sc-group-scheme-subgroup).
3. Write b=D(I+T). The inverse is triangular with inverse diagonal. In
   (bNb^-1)_ab=sum b_ap N_pq (b^-1)_qb, proper subintervals have smaller height.
   This proves normality and leaves precisely b_ii (b^-1)_jj N_ij at the next coordinate.
4. The same multiplication calculation makes p_r additive. Its section is I+aE_ij.
   The kernel ring is k[x_r,...,x_m] tensor_(k[t]) k=k[x_(r+1),...,x_m], where
   t maps to x_r and zero; this identifies the scheme-theoretic kernel.
5. The projection is flat by lem-nagata-polynomial-projection-flat. Its section proves
   surjectivity. Its finite polynomial presentation proves local finite presentation;
   lem-weil-pbc-affine-source-morphism-separated and
   lem-weil-pbc-affine-source-separated-target-affine-morphism show it is affine, and
   lem-weil-pbc-affine-morphism-permanence gives quasi-compactness and quasi-separatedness.
6. On each algebra, the section a maps to I+aE_ij and inverts the induced coset map.
   These maps are natural. The additive group is an fpqc sheaf by
   lem-weil-pbc-fpqc-representable-descent, hence an fppf sheaf by
   def-weil-pbc-fpqc-covering. The universal property def-weil-pbc-sheafification gives
   the quotient presentation IsFppfGroupQuotient, with its specified kernel square.
7. Triangular multiplication makes each diagonal entry a multiplicative character.
   The formula of step 3 factors the action through these diagonal coordinates, with
   character t_i/t_j. Diagonal entries of H 0 are one, proving its trivial action on
   every additive quotient. For n=1 there are no pairs and H 0 is the identity scheme.
-/
theorem unitriangular_coordinate_filtration (k : Type u) [Field k]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (C : Fin (n * (n - 1) / 2) ≃ {p : Fin n × Fin n // p.1 < p.2})
      (B : Grp (Over (Spec (.of k))))
      (β : B ⟶ Grp.mk (GeneralLinearGroup (LinearGroupSchemes.Index.{u} n) k))
      (H : Fin (n * (n - 1) / 2 + 1) → Grp (Over (Spec (.of k))))
      (inc : ∀ r, H r ⟶ B)
      (a : ∀ r : Fin (n * (n - 1) / 2), H r.succ ⟶ H r.castSucc)
      (p : ∀ r : Fin (n * (n - 1) / 2),
        H r.castSucc ⟶ Grp.mk (StandardGroupSchemes.additive k))
      (delta : Fin n → (B ⟶ Grp.mk (StandardGroupSchemes.multiplicative k))),
      (∀ l t, l < t ↔
        ((C l).val.2.val - (C l).val.1.val < (C t).val.2.val - (C t).val.1.val ∨
        ((C l).val.2.val - (C l).val.1.val = (C t).val.2.val - (C t).val.1.val ∧
          (C l).val.1 < (C t).val.1))) ∧
      IsClosedSubgroupScheme β.hom.hom ∧
      LocallyOfFiniteType B.X.hom ∧ QuasiCompact B.X.hom ∧
      (∀ (R : Type u) [CommRing R] [Algebra k R]
        (x : StandardGroupSchemes.affine k R ⟶
          GeneralLinearGroup (LinearGroupSchemes.Index.{u} n) k),
        (∃ b : StandardGroupSchemes.affine k R ⟶ B.X, b ≫ β.hom.hom = x) ↔
        ∀ i j : Fin n, j < i →
          GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} n) k R x ⟨i⟩ ⟨j⟩ = 0) ∧
      (∀ r, IsClosedSubgroupScheme (inc r).hom.hom ∧
        IsNormalSubgroupScheme (inc r).hom.hom ∧
        LocallyOfFiniteType (H r).X.hom ∧ QuasiCompact (H r).X.hom) ∧
      (∀ (r : Fin (n * (n - 1) / 2 + 1))
        (R : Type u) [CommRing R] [Algebra k R]
        (b : StandardGroupSchemes.affine k R ⟶ B.X),
        (∃ x : StandardGroupSchemes.affine k R ⟶ (H r).X, x ≫ (inc r).hom.hom = b) ↔
        (∀ i : Fin n,
          GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} n) k R
            (b ≫ β.hom.hom) ⟨i⟩ ⟨i⟩ = 1) ∧
        (∀ l : Fin (n * (n - 1) / 2), l.val < r.val →
          GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} n) k R
            (b ≫ β.hom.hom) ⟨(C l).val.1⟩ ⟨(C l).val.2⟩ = 0)) ∧
      IsIso (H (Fin.last (n * (n - 1) / 2))).X.hom ∧
      (∀ r, a r ≫ inc r.castSucc = inc r.succ) ∧
      (∀ r, IsClosedSubgroupScheme (a r).hom.hom ∧
        Flat (p r).hom.hom.left ∧ Surjective (p r).hom.hom.left ∧
        LocallyOfFinitePresentation (p r).hom.hom.left ∧
        QuasiCompact (p r).hom.hom.left ∧ QuasiSeparated (p r).hom.hom.left ∧
        IsFppfGroupQuotient (a r) (p r)) ∧
      (∀ (r : Fin (n * (n - 1) / 2))
        (R : Type u) [CommRing R] [Algebra k R]
        (x : StandardGroupSchemes.affine k R ⟶ (H r.castSucc).X),
        x ≫ (p r).hom.hom = StandardGroupSchemes.additiveCoordinatePoint k R
          (GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} n) k R
            (x ≫ (inc r.castSucc).hom.hom ≫ β.hom.hom)
            ⟨(C r).val.1⟩ ⟨(C r).val.2⟩)) ∧
      (∀ (R : Type u) [CommRing R] [Algebra k R]
        (b : StandardGroupSchemes.affine k R ⟶ B.X) (i : Fin n),
        StandardGroupSchemes.multiplicativeCoordinateValue k (b ≫ (delta i).hom.hom) =
          GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} n) k R
            (b ≫ β.hom.hom) ⟨i⟩ ⟨i⟩) ∧
      (∀ (r : Fin (n * (n - 1) / 2))
        (R : Type u) [CommRing R] [Algebra k R]
        (b : StandardGroupSchemes.affine k R ⟶ B.X)
        (x : StandardGroupSchemes.affine k R ⟶ (H r.castSucc).X),
        ∃ y : StandardGroupSchemes.affine k R ⟶ (H r.castSucc).X,
          y ≫ (inc r.castSucc).hom.hom = b * (x ≫ (inc r.castSucc).hom.hom) * b⁻¹ ∧
          y ≫ (p r).hom.hom = StandardGroupSchemes.additiveCoordinatePoint k R
            (StandardGroupSchemes.multiplicativeCoordinateValue k
                (b ≫ (delta (C r).val.1).hom.hom) *
              StandardGroupSchemes.multiplicativeCoordinateValue k
                (b⁻¹ ≫ (delta (C r).val.2).hom.hom) *
              GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} n) k R
                (x ≫ (inc r.castSucc).hom.hom ≫ β.hom.hom)
                ⟨(C r).val.1⟩ ⟨(C r).val.2⟩)) ∧
      (∀ (r : Fin (n * (n - 1) / 2))
        (R : Type u) [CommRing R] [Algebra k R]
        (b : StandardGroupSchemes.affine k R ⟶ (H 0).X)
        (x : StandardGroupSchemes.affine k R ⟶ (H r.castSucc).X),
        ∃ y : StandardGroupSchemes.affine k R ⟶ (H r.castSucc).X,
          y ≫ (inc r.castSucc).hom.hom =
            (b ≫ (inc 0).hom.hom) * (x ≫ (inc r.castSucc).hom.hom) * (b ≫ (inc 0).hom.hom)⁻¹ ∧
          y ≫ (p r).hom.hom = x ≫ (p r).hom.hom) ∧
      (n = 1 → IsIso (H 0).X.hom) := by
  sorry

end AlgebraicGeometry
