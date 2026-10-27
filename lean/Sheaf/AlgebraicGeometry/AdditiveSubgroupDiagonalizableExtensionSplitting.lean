module

public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Finiteness

import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur

/-! # Splitting diagonalizable extensions with an additive subgroup kernel

Source: Milne, Algebraic Groups (2017), Theorem 15.34(d), p.319, and its application
in Theorem 16.26(a), pp.332--333
(blueprint: lem-sfb-additive-subgroup-diagonalizable-extension-splitting).

The quotient presentation is the existing fppf group quotient. Scalar stability and
conjugation are tested on all commutative algebras, including nonreduced algebras.
The group law on points of Gₐ is written multiplicatively by the group-object API;
its coordinate is the usual additive coordinate of the affine line.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.StandardGroupSchemes

namespace AlgebraicGeometry

/-- An extension of D(M) by a closed additive subgroup with scalar conjugation splits.

Source: Milne, Algebraic Groups (2017), Theorem 15.34(d), p.319, with the
pullback-extension application in Theorem 16.26(a), pp.332--333
(blueprint: lem-sfb-additive-subgroup-diagonalizable-extension-splitting).

Proof plan (the eight steps of the DAG node):
1. Form the affine finite-type group $H=\mathbf G_a\rtimes E$ with multiplication
$(v,e)(w,f)=(v+\chi(q(e))w,ef)$ and inverse $(v,e)^{-1}=(-\chi(q(e))^{-1}v,e^{-1})$. These are
scheme morphisms and satisfy the group axioms by the character identity. The graph
$K=\{(-x,i(x)):x\in N\}$ is a closed subgroup isomorphic to $N$. Its normality is the explicit
identity $$(v,e)(-x,i(x))(v,e)^{-1}=(-\chi(q(e))x,i(\chi(q(e))x)).$$ Stability of $N$ makes the
right side an element of $K$ on every algebra. Apply the affine normal quotient theorem to
obtain the affine finite-type group $F=H/K$ and its fppf quotient map. Write $[v,e]$ for a local
representative; the brackets do not assert existence of a representative over the original
algebra.

2. The homomorphisms $u:\mathbf G_a\to F$, $v\mapsto[v,1]$, $j:E\to F$, $e\mapsto[0,e]$, and
$r:F\to D$, $[v,e]\mapsto q(e)$ satisfy $rj=q$. The formula for $r$ is invariant under $K$,
hence descends by the defining quotient-sheaf universal property. Both $u$ and $j$ are
monomorphisms: fppf locally membership of $(v,1)$ or $(0,e)$ in $K$ forces respectively $x=0$ or
$x=0$, and then $v=0$ or $e=1$. If $q(e)=1$, write $e=i(x)$; the relation $[v,i(x)]=[v+x,1]$
identifies $\ker r$ with $u(\mathbf G_a)$. Local surjectivity of $q$ shows that $r$ is locally
surjective as a sheaf map. Thus $D=F/u(\mathbf G_a)$ as fppf sheaves. The kernel is a closed
normal subgroup, and the quotient theorem says that $r$ is a faithfully flat finitely presented
$\mathbf G_a$-torsor. Conjugation on its kernel is $f u(v)f^{-1}=u(\chi(r(f))v)$, as follows
locally from the multiplication in $H$.

3. Here is the affine additive-torsor argument, with no new torsor lemma. Put $B=k[M]=\mathcal
O(D)$ and $C=\mathcal O(F)$; $B\to C$ is faithfully flat by the preceding step. The tautological
section $t_C$ over $\operatorname{Spec}C$ has two pullbacks related uniquely by $t_2=u(z)t_1$,
with $z\in C\otimes_B C$. On triple overlaps $z_{13}=z_{12}+z_{23}$. Amitsur exactness for $B\to
C$ with module $B$ gives $w\in C$ with $z=1\otimes w-w\otimes1$. Therefore $u(-w)t_C$ agrees on
the double overlap. To descend it, use affineness: its coordinate algebra map $\mathcal O(F)\to
C$ has image in the equalizer of $C\rightrightarrows C\otimes_B C$, which is $B$ by the same
exactness. Its unique factorization into $B$ preserves sums, products and scalars since $B\to C$
is injective. It defines a scheme section $t:D\to F$ of $r$. Translate $t$ on the left by
$t(1)^{-1}\in u(k)$ so that $t(1)=1$.

4. Define the regular function $c:D\times D\to\mathbf G_a$ by $t(x)t(y)=u(c(x,y))t(xy)$. The
torsor identity supplies $c$ as a scheme morphism, not merely as a rule on field-valued points.
Associativity and the preceding conjugation formula give
$$c(x,y)+c(xy,z)=\chi(x)c(y,z)+c(x,yz).$$ Let $\lambda:B\to k$ extract the coefficient of $e_0$,
and put $b=(\operatorname{id}_B\otimes\lambda)c\in B$. Since $\Delta(e_a)=e_a\otimes e_a$,
applying $\lambda$ in the second variable of $h(xy)$ gives the constant $\lambda(h)$ for any
$h\in B$. Apply $\lambda$ in the $z$ variable of the displayed identity to obtain
$$c(x,y)+b(xy)=\chi(x)b(y)+b(x).$$ Consequently $\sigma(d)=u(-b(d))t(d)$ satisfies
$\sigma(x)\sigma(y)=\sigma(xy)$ and $r\sigma=1_D$. The multiplicative identity also forces
$\sigma(1)=1$. This calculation uses the group-algebra basis, including when $D$ is nonreduced;
it does not average geometric points.

5. If $N=\mathbf G_a$, every $[v,e]$ is locally $[0,i(v)e]$. The monomorphism $j$ is therefore
an isomorphism of the represented quotient sheaves, so $j^{-1}\sigma$ is the required section of
$q$. Otherwise apply the monic additive-polynomial quotient node to the proper subgroup $N$,
with $G=D$ and $\eta=\chi$. Obtain its polynomial $P$ of positive degree $n$, kernel $N$, and
identity $P(\chi(d)v)=\chi(d)^nP(v)$. Put $\psi=\chi^n$.

6. In the proper-subgroup case the rule $a([v,e])=P(v)$ descends to a scheme morphism
$a:F\to\mathbf G_a$: replacing $(v,e)$ by $(v,e)(-x,i(x))$ replaces $v$ by $v-\chi(q(e))x$,
whose $P$-value is unchanged. The quotient universal property gives descent, and the
multiplication formula gives $$a(ff')=a(f)+\psi(r(f))a(f').$$ Its zero fibre is exactly $j(E)$
as a sheaf. Indeed, locally $a([v,e])=0$ means $v\in N$, and then $[v,e]=[0,i(v)e]$. Conversely
$a([0,e])=0$. The monomorphism property of $j$ makes the local preimage unique, so these
preimages glue in the sheaf represented by $E$. This also shows that $j$ identifies $E$ with the
scheme-theoretic zero fibre, including on nonreduced test algebras.

7. Let $f=a\sigma\in B$ and let $\alpha=\lambda(f)\in k$, using the same coefficient functional
as above. Since $\sigma$ is a homomorphism, $f(xy)=f(x)+\psi(x)f(y)$. Apply $\lambda$ in the $y$
variable. The left side is $\alpha$, hence $f(x)=\alpha(1-\psi(x))$. The polynomial
$P(T)-\alpha$ is nonconstant, so algebraic closedness gives $v\in k$ with $P(v)=\alpha$.

8. Conjugate the homomorphism $\sigma$ by $u(-v)$, setting $\sigma'(d)=u(-v)\sigma(d)u(v)$. It
still satisfies $r\sigma'=1_D$, and the crossed identity for $a$ gives
$$a(\sigma'(d))=-P(v)+f(d)+\psi(d)P(v)=0.$$ The zero-fibre identification from step 6 therefore
factors $\sigma'$ uniquely as $j\circ s$ for a scheme morphism $s:D\to E$. Since $j$ is a
group-scheme monomorphism and $\sigma'$ a homomorphism, $s(xy)=s(x)s(y)$ and $s(1)=1$. Finally
$q\circ s=rj\circ s=r\sigma'=1_D$. -/
theorem additiveSubgroup_diagonalizable_extension_splits
    {k : Type u} [Field k] [IsAlgClosed k]
    (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (N E : Grp (Over (Spec (.of k))))
    [IsAffine N.X.left] [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    [IsAffine E.X.left] [LocallyOfFiniteType E.X.hom] [QuasiCompact E.X.hom]
    (j : N.X ⟶ additive k) [IsClosedSubgroupScheme j]
    (chi : (diagonalizableGroup k M).X ⟶ multiplicative k) [IsMonHom chi]
    (i : N ⟶ E) [IsClosedSubgroupScheme i.hom.hom]
    [IsNormalSubgroupScheme i.hom.hom]
    (q : E ⟶ diagonalizableGroup k M) (hquot : IsFppfGroupQuotient i q)
    (hstable : ∀ (R : Type u) [CommRing R] [Algebra k R]
        (d : affine k R ⟶ (diagonalizableGroup k M).X) (x : R),
      (∃ z : affine k R ⟶ N.X, z ≫ j = additiveCoordinatePoint k R x) →
      ∃ z : affine k R ⟶ N.X, z ≫ j = additiveCoordinatePoint k R
        (multiplicativeCoordinateValue k (d ≫ chi) * x))
    (hconj : ∀ (R : Type u) [CommRing R] [Algebra k R]
        (e : affine k R ⟶ E.X) (x : R) (z : affine k R ⟶ N.X),
      z ≫ j = additiveCoordinatePoint k R x →
      ∃ w : affine k R ⟶ N.X,
        w ≫ j = additiveCoordinatePoint k R
          (multiplicativeCoordinateValue k (e ≫ q.hom.hom ≫ chi) * x) ∧
        e * (z ≫ i.hom.hom) * e⁻¹ = w ≫ i.hom.hom) :
    ∃ s : diagonalizableGroup k M ⟶ E, s ≫ q = 𝟙 (diagonalizableGroup k M) := by
  sorry

end AlgebraicGeometry
