/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.SemisimpleLieElement
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.AlgebraicGeometry.GroupScheme.LieLocalDimension
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # A smaller nonunipotent semisimple centralizer over an infinite field

Source: Milne, Algebraic Groups (2017), 17.76--17.79, pp.377--378, and 17.81, p.379;
1.34, pp.16--17, for the identity component; 14.5, pp.281--282, for unipotence
(blueprint: lem-sfb-infinite-field-semisimple-centralizer-reduction).

The stabilizer is specified on every algebra by commutation of the constant lift of g
with the scalar-extended tangent point of X. By the defining dual-number formula for Ad,
this is exactly Ad(g)(X tensor 1) = X tensor 1. The open immersion j specifies the actual
open-subscheme structure on the identity component of C, including when C is disconnected.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- The identity component of a suitable rational semisimple Lie-element centralizer is a
smooth connected closed subgroup of strictly smaller dimension and is not unipotent.
Source: Milne, Algebraic Groups (2017), 17.76--17.79 and 17.81, pp.377--379;
1.34, pp.16--17; 14.5, pp.281--282
(blueprint: lem-sfb-infinite-field-semisimple-centralizer-reduction).

Proof (the eight steps of the DAG node):
1. Choose a closed embedding $i:G\hookrightarrow\operatorname{GL}_{m,k}$ by
[lem-sfb-affine-group-faithful-linear-representation]. By
[lem-sfb-affine-group-dual-number-calculus] its differential is injective, so identify $\mathfrak
g$ with a matrix subspace. The dual-number conjugation formula gives
$\operatorname{Ad}(g)Z=gZg^{-1}$ and, on differentiating, $\operatorname{ad}(Y)Z=YZ-ZY$. Choose a
basis of $\mathfrak g$, of dimension $d$. The coefficients $f_1,\ldots,f_d$ in
$$\det(T-\operatorname{ad}(Y))=T^d+f_1(Y)T^{d-1}+\cdots+f_d(Y)$$ are polynomial functions of the
coordinates of $Y$: the entries of $\operatorname{ad}(Y)$ are linear and the determinant is its
permutation sum. For the given geometric noncentral semisimple element
$S\in\operatorname{Lie}(G_{\bar k})=\mathfrak g\otimes_k\bar k$, its image under some faithful
closed representation of $G_{\bar k}$ is diagonalizable; the arbitrary-field faithful detection
clause of [lem-sfb-algebraic-lie-additive-jordan], applied over $\bar k$ to that closed immersion
and to the rational representation $i_{\bar k}$, shows that $di(S)$ is diagonalizable. Diagonalize
$di(S)$. Commutation on all matrices is diagonal in the matrix-unit basis, with eigenvalues the
differences of its diagonal entries. Its invariant subspace $\mathfrak g_{\bar k}$ is a sum of
eigenspaces, by polynomial spectral projections. Hence $\operatorname{ad}(S)$ is diagonalizable
and nonzero. Some eigenvalue is nonzero, so its characteristic polynomial is not $T^d$. Thus some
$f_i$ is nonzero.
2. Choose such a nonzero coefficient $f_i\in k[y_1,\ldots,y_d]$. A nonzero polynomial over an
infinite field cannot vanish at every rational tuple: induct on the number of variables, choose
values of the first $d-1$ variables making one nonzero coefficient in the last variable nonzero,
and then avoid the finitely many roots of the resulting nonzero one-variable polynomial. For zero
variables a nonzero constant already has nonzero value. Consequently choose $Y\in\mathfrak g(k)$
with $f_i(Y)\ne0$. Then $\operatorname{ad}(Y)$ has a nonzero eigenvalue over $\bar k$.
3. If $\operatorname{char}k=0$, apply [lem-sfb-algebraic-lie-additive-jordan] to $Y$ over the
perfect field $k$ and put $X=Y_s$. Functoriality for the adjoint representation says that
$\operatorname{ad}(X)$ is the semisimple part of $\operatorname{ad}(Y)$; its nonzero eigenvalue
from step 2 persists, so $X$ is noncentral. If $\operatorname{char}k=p>0$, use
[lem-sfb-restricted-rational-differentiation] and put $X=Y^{[p^N]}$ for sufficiently large $N$. It
lies in $\mathfrak g(k)$ and $di(X)=di(Y)^{p^N}$, while
$\operatorname{ad}(X)=\operatorname{ad}(Y)^{p^N}$. Apply [lem-sfb-algebraic-lie-additive-jordan]
over $\bar k$ to write $di(Y)=M_s+M_n$ with commuting diagonalizable $M_s$ and nilpotent $M_n$.
Choose $p^N$ at least a nilpotence exponent of $M_n$. The binomial formula in characteristic $p$
gives $di(X)=M_s^{p^N}$, which is diagonalizable; and the nonzero eigenvalue of
$\operatorname{ad}(Y)$ remains nonzero on raising it to $p^N$. Thus also in this case $X$ is
rational, semisimple and noncentral. No Jordan part is assumed rational over an imperfect field.
4. Put $M=di(X)$ and write $G=\operatorname{Spec}A$. Let $I\subseteq A$ be generated by the
entries of $gM-Mg$ of the universal matrix $g\in G(A)$. Then $C=\operatorname{Spec}(A/I)$ is
closed, affine and of finite type; it represents the required adjoint stabilizer on every
commutative $k$-algebra, by the matrix formula and tangent injectivity in
[lem-sfb-affine-group-dual-number-calculus]. A product or inverse of matrices commuting with $M$
again commutes with $M$, so the group laws restrict, giving a closed subgroup. For $Z\in\mathfrak
g$, the element $1+\epsilon\,di(Z)$ belongs to $C(k[\epsilon]/\epsilon^2)$ exactly when
$di(Z)M-Mdi(Z)=0$. Therefore $$\operatorname{Lie}(C)=\{Z\in\mathfrak g:[Z,X]=0\}.$$ Noncentrality
makes this a proper subspace, and in particular $C\ne G$.
5. Infinitesimal conjugation by $1+\epsilon M$ induces a derivation $D:A\to A$, since it is an
algebra automorphism over the dual numbers reducing to the identity;
[lem-sfb-affine-group-dual-number-calculus] ensures that this conjugation preserves $G$. On
universal matrix entries it has values $(Mg-gM)_{ab}$, and on $\det(g)^{-1}$ it is zero, since
determinant is invariant under conjugation. These elements generate $A$ as an algebra, so the
Leibniz rule gives $I=(D(A))$. Over $\bar k$, write $M=PZP^{-1}$ with $Z$ diagonal, with diagonal
entries $\lambda_a$, and use the coordinates $x'=P^{-1}xP$. On $\bar k[x'_{ab},\det(x')^{-1}]$,
$D$ is diagonal on monomials: $x'_{ab}$ has eigenvalue $\lambda_a-\lambda_b$ and $\det(x)^{-1}$
has eigenvalue zero. The defining ideal of $G_{\bar k}$ is $D$-stable, because infinitesimal
conjugation preserves the subgroup. A stable subspace of this direct sum of eigenspaces is a sum
of its eigenspaces: for each vector its finitely many eigencomponents are recovered by Lagrange
interpolation polynomials in $D$. Thus the quotient $A\otimes_k\bar k$ also has an eigenspace
decomposition for $D$. Apply [lem-sfb-semisimple-derivation-zero-smooth] to this smooth affine
algebra $A$ to conclude that $C=\operatorname{Spec}(A/I)$ is smooth over $k$.
6. Apply [lem-sfb-finite-type-group-identity-subgroup] to the finite-type group $C$. Its identity
component $K=C^\circ$ is a connected open and closed subgroup scheme. By
[lem-pc-open-immersion-smooth-composition] it is smooth. The closed immersions into $C$ and then
$G$ exhibit it as a closed affine finite-type subgroup: on affine coordinate rings these are
successive quotients. Its tangent space at the identity is the same as that of $C$. Indeed the
image of every dual-number tangent map has just the identity as its underlying point, and hence
factors uniquely through the open subscheme $K$ by
[lem-weil-pbc-morphism-factors-through-open-subscheme]; this factorization is inverse to the
tangent map of $K\hookrightarrow C$. Therefore $\operatorname{Lie}(K)=\operatorname{Lie}(C)$ as
subspaces of $\mathfrak g$.
7. For $J=K,G$, smoothness and [lem-ag-smooth-lie-local-dimension] give
$\dim_k\operatorname{Lie}(J)=\dim\mathcal O_{J,e}$, and [lem-ag-group-identity-local-dimension]
identifies the latter with $\dim J$. Step 4 and step 6 make
$\operatorname{Lie}(K)=\ker(\operatorname{ad}(X))$ a proper subspace of the finite-dimensional
$\mathfrak g$. Extend a basis of this kernel by a vector outside it and then to a basis of
$\mathfrak g$; consequently $$\dim K=\dim_k\ker\operatorname{ad}(X)<\dim_k\mathfrak g=\dim G.$$
Both cited dimension results allow arbitrary fields; no algebraically closed or
characteristic-zero specialization is being used.
8. The alternating bracket gives $[X,X]=0$, so step 4 and step 6 put $X$ in
$\operatorname{Lie}(K)$; noncentrality gives $X\ne0$. If $K$ were unipotent as in the statement,
choose its closed embedding into $\mathcal U_{n,k}\subset\operatorname{GL}_{n,k}$. Its tangent
matrices are strictly upper triangular: substituting $1+\epsilon N$ in the defining equations sets
diagonal and lower entries of $N$ to zero. Thus the image of $X$ is nilpotent. The arbitrary-field
faithful detection assertion of [lem-sfb-algebraic-lie-additive-jordan], applied to $K$, forces
the image of $X$ in the original faithful representation $i|_K$ to be nilpotent as well. That
image is the diagonalizable matrix $M$ of step 3. A diagonalizable nilpotent matrix has every
eigenvalue zero and is therefore zero. Tangent injectivity of $di$ from
[lem-sfb-affine-group-dual-number-calculus] gives $X=0$, a contradiction. Hence $K$ is not
unipotent. -/
theorem exists_semisimple_lie_centralizer_reduction
    {k : Type u} [Field k] [Infinite k]
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hgeom : ∃ S : GrpObj.Lie ((MultiplicativeType.baseChange (K := Ω)).obj G).X,
      GrpObj.HasDiagonalizableFaithfulLieImage Ω
        ((MultiplicativeType.baseChange (K := Ω)).obj G) S ∧
      ∃ Y : GrpObj.Lie ((MultiplicativeType.baseChange (K := Ω)).obj G).X, ⁅S, Y⁆ ≠ 0) :
    ∃ X : GrpObj.Lie G.X, GrpObj.HasDiagonalizableFaithfulLieImage Ω G X ∧
      (∃ Y : GrpObj.Lie G.X, ⁅X, Y⁆ ≠ 0) ∧
      ∃ (C : Grp (Over (Spec (.of k)))) (i : C ⟶ G),
        IsClosedSubgroupScheme i.hom.hom ∧ ¬ IsIso i.hom.hom.left ∧
        IsAffine C.X.left ∧ LocallyOfFiniteType C.X.hom ∧ QuasiCompact C.X.hom ∧
        Smooth C.X.hom ∧
        (∀ (R : Type u) [CommRing R] [Algebra k R] (g : points G.X R),
          (∃ c : points C.X R, c ≫ i.hom.hom = g) ↔
            points.map G.X (TrivSqZeroExt.inlAlgHom k R R) g *
                points.map G.X
                  (AffineGroupDualNumberCalculus.dualMap (Algebra.ofId k R))
                  (GrpObj.tangentPoint X) =
              points.map G.X
                  (AffineGroupDualNumberCalculus.dualMap (Algebra.ofId k R))
                  (GrpObj.tangentPoint X) *
                points.map G.X (TrivSqZeroExt.inlAlgHom k R R) g) ∧
        ∃ (K : Grp (Over (Spec (.of k)))) (j : K ⟶ C),
          IsOpenImmersion j.hom.hom.left ∧
          Set.range j.hom.hom.left = connectedComponent (GrpObj.onePoint C.X) ∧
          IsClosedSubgroupScheme (j ≫ i).hom.hom ∧
          IsAffine K.X.left ∧ LocallyOfFiniteType K.X.hom ∧ QuasiCompact K.X.hom ∧
          Smooth K.X.hom ∧ ConnectedSpace K.X.left ∧
          topologicalKrullDim K.X.left < topologicalKrullDim G.X.left ∧
          ¬ (∃ n : ℕ, 0 < n ∧
            ∃ r : K ⟶ Grp.mk (GeneralLinearGroup (ULift.{u} (Fin n)) k),
              IsClosedSubgroupScheme r.hom.hom ∧
              ∀ (R : Type u) [CommRing R] [Algebra k R] (x : points K.X R),
                (∀ a : Fin n,
                  (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R
                    (x ≫ r.hom.hom)).val ⟨a⟩ ⟨a⟩ = 1) ∧
                (∀ a b : Fin n, b < a →
                  (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R
                    (x ≫ r.hom.hom)).val ⟨a⟩ ⟨b⟩ = 0)) := by
  sorry

end AlgebraicGeometry
