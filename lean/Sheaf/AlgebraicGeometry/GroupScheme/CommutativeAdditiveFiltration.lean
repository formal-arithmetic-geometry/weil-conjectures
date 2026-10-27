module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization

/-! # Additive subgroup factors in the absence of diagonalizable subgroups

Source: Milne, Algebraic Groups (2017), Theorem 16.13(a),(b), printed p.328,
and Proposition 14.21, printed pp.284--285
(blueprint: lem-sfb-commutative-no-diagonalizable-additive-filtration).

The finite chain retains its closed inclusions into G, its successive inclusions,
and its actual quotient maps. The quotient presentation includes the cartesian
kernel square and the sheafification universal property for the coset presheaf.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A commutative affine finite-type group with no nontrivial diagonalizable
closed subgroup has a finite filtration with closed additive subgroup factors.

Source: Milne, Algebraic Groups (2017), Theorem 16.13(a),(b), printed p.328,
Proposition 14.21, printed pp.284--285, and Theorem 5.39, printed p.108
(blueprint: lem-sfb-commutative-no-diagonalizable-additive-filtration).

Proof plan:
1. Apply lem-sfb-commutative-diagonalizable-unipotent-product. Its diagonalizable
   subgroup is trivial by the hypothesis, so the product decomposition identifies
   G with its unipotent subgroup and supplies a closed embedding in some U_n.
2. Use lem-sfb-unitriangular-coordinate-filtration, with m = n(n-1)/2 coordinates.
   If G = Spec A and x_l is the pullback of the l-th coordinate, set
   H_r = Spec (A/(x_1,...,x_r)). These are the closed inverse images of U^(r),
   hence closed subgroup schemes (def-sc-group-scheme-subgroup). Their coordinate
   algebras are finite type because they are quotients of A. The endpoints are
   H_0 = G and H_m = 1, since G embeds in U_n and U^(m) = 1.
3. Restrict the r-th coordinate homomorphism to H_(r-1) -> Ga. Its kernel is H_r,
   since its zero equation is x_r = 0. The affine source is separated by
   lem-weil-pbc-affine-source-morphism-separated. Apply
   lem-sfb-algebraic-group-homomorphism-factorization to obtain the faithfully
   flat finitely presented quotient q_r onto a closed subgroup I_r of Ga,
   with the specified kernel and fppf coset-sheaf quotient. The closed subscheme
   I_r of the affine line is affine and is finite type by that theorem.
4. Reverse the indices, taking s = m, G_j = H_(m-j), Q_j = I_(m-j+1), and
   q_j = q_(m-j+1). All the kernel, quotient and closed-embedding conditions
   then have the required orientation. For G = 1 take s = 0 and no quotient
   data. This argument does not use smoothness or connectedness.

Triviality is expressed by the structure morphism being an isomorphism to Spec k.
Testing the diagonalizable hypothesis on the standard D_k(M) suffices because a
closed subgroup isomorphic to it transports its inclusion along that isomorphism.
The endpoint G_s = G is expressed by its closed inclusion being an isomorphism. -/
theorem commutative_no_diagonalizable_additive_filtration
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (hdiag : ∀ (M : Type u) [AddCommGroup M] [AddGroup.FG M]
      (i : diagonalizableGroup k M ⟶ G),
      IsClosedSubgroupScheme i.hom.hom → IsIso (diagonalizableGroup k M).X.hom) :
    ∃ (s : ℕ) (H : Fin (s + 1) → Grp (Over (Spec (.of k))))
      (ι : ∀ j : Fin (s + 1), H j ⟶ G)
      (a : ∀ j : Fin s, H j.castSucc ⟶ H j.succ)
      (Q : Fin s → Grp (Over (Spec (.of k))))
      (q : ∀ j : Fin s, H j.succ ⟶ Q j)
      (b : ∀ j : Fin s, Q j ⟶ Grp.mk (StandardGroupSchemes.additive k)),
      (∀ j : Fin (s + 1), IsClosedSubgroupScheme (ι j).hom.hom) ∧
      IsIso (H 0).X.hom ∧ IsIso (ι (Fin.last s)).hom.hom.left ∧
      (∀ j : Fin s, a j ≫ ι j.succ = ι j.castSucc) ∧
      (∀ j : Fin s, IsClosedSubgroupScheme (a j).hom.hom) ∧
      (∀ j : Fin s, IsAffine (Q j).X.left ∧
        LocallyOfFiniteType (Q j).X.hom ∧ QuasiCompact (Q j).X.hom ∧
        Flat (q j).hom.hom.left ∧ Surjective (q j).hom.hom.left ∧
        LocallyOfFinitePresentation (q j).hom.hom.left ∧
        QuasiCompact (q j).hom.hom.left ∧ QuasiSeparated (q j).hom.hom.left ∧
        IsClosedSubgroupScheme (b j).hom.hom ∧ IsFppfGroupQuotient (a j) (q j)) := by
  sorry

end AlgebraicGeometry
