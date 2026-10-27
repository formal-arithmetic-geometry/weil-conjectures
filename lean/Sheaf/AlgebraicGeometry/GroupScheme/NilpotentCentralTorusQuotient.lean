module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange
import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# A central torus with unipotent quotient in a nilpotent algebraic group

Source: Milne, Algebraic Groups (2017), Theorem 16.47(a),(c), printed p.341;
Theorem 14.5(a),(b), pp.281--282; Propositions 5.25--5.29, p.105
(blueprint: lem-sfb-nilpotent-central-torus-quotient).

Nilpotence is stated using a finite descending series of closed normal subgroup schemes,
with commutator containment over every commutative algebra. The output embedding in GL_n
satisfies the unitriangular equations on every algebra, so factors as a closed immersion
into U_n. The quotient predicate retains the scheme-theoretic kernel square and the
universal property of fppf sheafification of the coset presheaf.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth connected nilpotent affine algebraic group over any field has a central
closed torus and a smooth connected unipotent represented fppf quotient. The displayed
quotient map is an isomorphism when its torus kernel is trivial.

Source: Milne, Algebraic Groups (2017), Theorem 16.47(a),(c), printed p.341,
as used in Proposition 17.81, p.379; Theorem 14.5(a),(b), pp.281--282;
Propositions 5.25--5.29, p.105
(blueprint: lem-sfb-nilpotent-central-torus-quotient).

Proof, following the seven steps of the DAG node:
1. Form the affine commutative centre Z of G by
   lem-sfb-affine-group-centre-base-change. Its largest multiplicative-type subgroup
   T = Z_s is central by lem-sfb-commutative-multiplicative-part. Apply
   lem-sfb-affine-normal-quotient-geometry to form the affine finite-type represented
   fppf quotient q : G -> Q with scheme-theoretic kernel T and faithfully flat q.
2. The hypotheses of lem-sfb-nilpotent-quotient-unipotent-centre hold because T
   contains every multiplicative-type subgroup of Z. Thus Q is connected and nilpotent
   with unipotent centre. By lem-sfb-nilpotent-unipotent-centre it embeds as a closed
   subgroup in U_m for some m >= 1. Quotient geometry makes Q smooth since G is smooth.
3. Extend to the algebraic closure F. Smoothness survives base change, and the rational
   identity point makes G_F connected by the connected-rational-point criterion.
   The given central series stays central on every F-algebra. Each factor is
   commutative, since [G_i,G_i] lies in [G,G_i], so G_F is solvable. Apply
   lem-sfb-lie-kolchin-triangular-embedding and lem-sfb-triangular-diagonal-kernel:
   there is a diagonal quotient d : G_F -> D with unipotent kernel V and a group
   section s : D -> G_F, where D is smooth connected and closed in a split torus.
4. By lem-sfb-split-torus-subgroups-diagonalizable, D is diagonalizable. The closed
   embedding Q -> U_m remains closed after extension to F. By
   lem-sfb-diagonalizable-to-unipotent-trivial, q_F s is trivial. Hence s factors
   through the kernel T_F as j : D -> T_F, and (d restricted to T_F) j = id.
5. The kernel I of d restricted to T_F is T_F intersect V, so embeds in U_n and is
   unipotent. Its inclusion into the multiplicative-type group T_F is trivial by
   lem-sfb-unipotent-to-multiplicative-trivial. Since it is injective on all algebra
   points, I is trivial. For t in T_F(A), t j(d(t))^(-1) lies in I(A), whence
   t = j(d(t)). These natural equalities make j inverse to d restricted to T_F.
6. Thus T_F is isomorphic to D. By lem-sfb-multiplicative-type-largest-subtorus,
   a smooth connected subgroup of a split torus is a torus. Over F it is G_m^r
   for some r >= 0, exactly the defining torus condition on T over k.
7. If T is trivial, its coset presheaf is the represented functor G. Representable
   functors are fppf sheaves, so the quotient's sheafification unit is an isomorphism.
   Yoneda then makes q an isomorphism of group schemes. No step requires k perfect. -/
theorem nilpotent_central_torus_quotient
    (k : Type u) [Field k] (G : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hseries : ∃ (s : ℕ) (H : Fin (s + 1) → Grp (Over (Spec (.of k))))
      (i : ∀ j : Fin (s + 1), H j ⟶ G),
      (∀ j : Fin (s + 1), IsClosedSubgroupScheme (i j).hom.hom ∧
        IsNormalSubgroupScheme (i j).hom.hom) ∧
      IsIso (i 0) ∧ Nonempty (H (Fin.last s) ≅ Grp.trivial _) ∧
      (∀ j : Fin s, ∃ l : H j.succ ⟶ H j.castSucc, l ≫ i j.castSucc = i j.succ) ∧
      ∀ (j : Fin s) (A : Type u) [CommRing A] [Algebra k A]
        (g : StandardGroupSchemes.affine k A ⟶ G.X)
        (h : StandardGroupSchemes.affine k A ⟶ (H j.castSucc).X),
        ∃ z : StandardGroupSchemes.affine k A ⟶ (H j.succ).X,
          z ≫ (i j.succ).hom.hom =
            g * (h ≫ (i j.castSucc).hom.hom) * g⁻¹ *
              (h ≫ (i j.castSucc).hom.hom)⁻¹) :
    ∃ (T Q : Grp (Over (Spec (.of k)))) (iT : T ⟶ G) (q : G ⟶ Q),
      IsAffine T.X.left ∧ LocallyOfFiniteType T.X.hom ∧ QuasiCompact T.X.hom ∧
      IsClosedSubgroupScheme iT.hom.hom ∧ MultiplicativeType.IsTorus T ∧
      (∀ (A : Type u) [CommRing A] [Algebra k A]
        (t : StandardGroupSchemes.affine k A ⟶ T.X)
        (g : StandardGroupSchemes.affine k A ⟶ G.X), Commute (t ≫ iT.hom.hom) g) ∧
      IsAffine Q.X.left ∧ LocallyOfFiniteType Q.X.hom ∧ QuasiCompact Q.X.hom ∧
      Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧
      (∃ n : ℕ, 0 < n ∧
        ∃ r : Q.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
          IsClosedSubgroupScheme r ∧
          ∀ (A : Type u) [CommRing A] [Algebra k A]
            (x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ Q.X),
            (∀ a : Fin n,
              (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ r)).val
                ⟨a⟩ ⟨a⟩ = 1) ∧
            ∀ a b : Fin n, b < a →
              (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ r)).val
                ⟨a⟩ ⟨b⟩ = 0) ∧
      Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
      IsFppfGroupQuotient iT q ∧
      (Nonempty (T ≅ Grp.trivial _) → IsIso q) := by
  sorry

end AlgebraicGeometry
