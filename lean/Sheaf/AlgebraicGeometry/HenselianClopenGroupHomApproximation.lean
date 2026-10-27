module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.RingTheory.FinitePresentation
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.GRing
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.HenselianPairApproximation

/-! # Henselian approximation of a clopen affine group homomorphism

Source: Stacks Project, Smoothing Ring Maps, Tag 0AH5 (lemma-henselian-pair),
via the finite polynomial certificates specified in the DAG proof
(blueprint: lem-sfb-henselian-clopen-group-hom-approximation).

The residue comparison first extends the sought map to the completion and then
pulls both maps back along the canonical projection to the residue field. By
composition of pullbacks, this is exactly equality of the original special-fibre
maps under the canonical completion-residue identification.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Approximate a given clopen homomorphism over the maximal-ideal completion by
one over the henselian local G-ring with the same residue homomorphism.

Source: Stacks Project, Tag 0AH5, order one, and the following finite-certificate
argument (blueprint: lem-sfb-henselian-clopen-group-hom-approximation).

Proof:
1. Choose finite presentations $P=A[x_1,\ldots,x_n]/(r_1,\ldots,r_a)$ and
$Q=A[y_1,\ldots,y_m]/(s_1,\ldots,s_b)$. For any $A$-algebra $R$, put $P_R=R\otimes_AP$ and
$Q_R=R\otimes_AQ$. The affine fibre-product theorem identifies their spectra with $X_R,Y_R$. The
universal property of tensor product and polynomial evaluation identifies $P_R$ with $R[x]/(r)$:
maps from either algebra to an $R$-algebra are precisely tuples satisfying the $r_i$; the
mutually inverse maps send each variable to its namesake. Likewise $Q_R=R[y]/(s)$ and
$P_R\otimes_RP_R=R[x,x']/(r(x),r(x'))$. These presentations hold for every $R$; no flatness is
used. Uses: def-weil-pbc-finitely-presented-algebra, def-weil-pbc-mv-polynomial-ring,
def-weil-affine-spectrum, lem-weil-pbc-fibre-product-affine-spectra.

2. Write $f^{\wedge}:Q_{\widehat A}\to P_{\widehat A}$ for the algebra map of $v$. Its image
$U\subseteq\operatorname{Spec}Q_{\widehat A}$ is clopen, and $v$ identifies its source with the
open subscheme $U$. Choose the idempotent $e^{\wedge}$ with $U=D(e^{\wedge})$. The
affine-basic-open theorem identifies restriction to $U$ with localization at $e^{\wedge}$. For
any idempotent $e$ in a ring $B$, the map $B\to B_e$ is surjective and has kernel $(1-e)B$: in
$B_e$ one has $e=1$, and $b/e^d=b/1$, while $e^db=0$ implies $b=(1-e)b$ (the case $d=0$ gives
$b=0$). Thus $f^{\wedge}$ induces $Q_{\widehat A}/(1-e^{\wedge})\simeq P_{\widehat A}$. Uses:
def-weil-affine-spectrum, lem-weil-pbc-spec-clopen-idempotent,
lem-weil-pbc-affine-open-section-vanishing-prime, def-weil-open-immersion,
def-weil-closed-immersion.

3. Multiplication by $e^{\wedge}$ identifies $Q_{\widehat A}/(1-e^{\wedge})$ with the corner
$e^{\wedge}Q_{\widehat A}$, whose identity is $e^{\wedge}$: the inverse sends $e^{\wedge}q$ to
the class of $q$. Composing the inverse of the preceding isomorphism with this corner inclusion
gives an additive multiplicative $\widehat A$-linear map $g^{\wedge}:P_{\widehat A}\to
Q_{\widehat A}$ with $g^{\wedge}(1)=e^{\wedge}$, $f^{\wedge}g^{\wedge}=1$, and
$g^{\wedge}f^{\wedge}(q)=e^{\wedge}q$. Here $g^{\wedge}$ is allowed to be nonunital. Choose
polynomial representatives $F_j(x)$ of $f^{\wedge}(y_j)$, $G_i(y)$ of $g^{\wedge}(x_i)$, and
$E(y)$ of $e^{\wedge}$, all with coefficients in $\widehat A$. Fix their finite monomial
supports; their coefficients will be unknowns. Uses: def-weil-pbc-algebra-hom-quotient,
def-weil-pbc-mv-polynomial-ring.

4. For coefficients in any $A$-algebra $R$, use the same supports for $F_j,G_i,E$. Impose
$s_l(F)\in(r)$, $E^2-E\in(s)$, and $EG_i-G_i\in(s)$. For $p(x)=\sum_\alpha c_\alpha x^\alpha$,
write $T(p)=c_0E+\sum_{\alpha\ne0}c_\alpha G^\alpha$ and impose $T(r_l)\in(s)$ for every
relation of $P$. Then $f:Q_R\to P_R$, $y_j\mapsto F_j$, is a unital algebra map. Modulo $(s)$
the relations $E^2=E$ and $EG_i=G_i$ make $T$ additive, $R$-linear and multiplicative, with
$T(1)=E$: multiply two monomials, treating a constant as a multiple of $E$. Since
$T(r_lh)=T(r_l)T(h)$, it annihilates $(r)$ and induces $g:P_R\to Q_R$ with $g(1)=E$. Uses:
def-weil-pbc-finitely-presented-algebra, def-weil-pbc-mv-polynomial-ring,
def-weil-pbc-algebra-hom-quotient.

5. Also impose $E(F)-1\in(r)$, $G_i(F)-x_i\in(r)$ and $T(F_j)-Ey_j\in(s)$. The first two sets
say $fg=1_{P_R}$, since both sides are unital $R$-algebra maps agreeing on $x_i$. The third set
says $gf(q)=Eq$ for all $q\in Q_R$: both maps are additive multiplicative $R$-linear maps with
value $E$ at $1$, and they agree on $y_j$, hence on all polynomial expressions. These are finite
lists even if some presentation has no generators or no relations. The chosen completion
coefficients satisfy every imposed condition by their construction. Uses:
def-weil-pbc-mv-polynomial-ring, def-weil-pbc-algebra-hom-quotient.

6. Represent the fixed multiplication, identity and inverse maps of $X$ by polynomials
$D_i^P(x,x')$, elements $c_i^P\in A$, and polynomials $I_i^P(x)$, respectively. Represent those
of $Y$ by $D_j^Q(y,y')$, $c_j^Q$, $I_j^Q(y)$. This is possible by the presentations in Step 1
and the affine-spectrum correspondence. Impose, for each $j$, the three further identities
$$F_j(D^P(x,x'))-D_j^Q(F(x),F(x'))\in(r(x),r(x')),$$ $$F_j(c^P)-c_j^Q=0,\qquad
F_j(I^P(x))-I_j^Q(F(x))\in(r).$$ They say exactly $\Delta_Pf=(f\otimes f)\Delta_Q$,
$\epsilon_Pf=\epsilon_Q$, and $S_Pf=fS_Q$, checked on the generators $y_j$. Dualizing by the
affine-spectrum correspondence gives compatibility with multiplication, identity and inverse.
The given $v$ satisfies these equations. Neither cocommutativity of $\Delta$ nor any flatness is
needed. Uses: def-weil-affine-spectrum, lem-weil-pbc-fibre-product-affine-spectra,
def-weil-pbc-finitely-presented-algebra, def-weil-pbc-mv-polynomial-ring.

7. Each requirement above, other than a scalar equality, has the form $H\in(t_1,\ldots,t_d)$ in
a polynomial ring over $R$, where the fixed list $t$ is $(r(x))$, $(s(y))$ or $(r(x),r(x'))$. At
the given completion solution choose actual polynomial witnesses $B_1,\ldots,B_d$ with $H=\sum_l
B_lt_l$. This is exactly membership in the ideal generated by $t$. Choose such witnesses for
every requirement, a finite list, and fix each witness's finite monomial support. For the empty
list of relations, membership means the polynomial $H$ itself is zero and no witnesses are
required. Introduce one more unknown for each witness coefficient. Uses:
def-weil-pbc-algebra-hom-quotient, def-weil-pbc-mv-polynomial-ring.

8. Replace every membership requirement by the polynomial identity $H-\sum_lB_lt_l=0$, and
compare coefficients of all monomials occurring in that expression. Each coefficient is a
polynomial over $A$ in the finitely many unknown coefficients of $F,G,E$ and the witnesses:
substitution, multiplication and addition of finite polynomials use finitely many sums and
products. Include the scalar equations from Step 6. Thus there is one finite system
$h_1(z)=\cdots=h_c(z)=0$ over $A$ with a specified solution $\widehat z$ in $\widehat A$. Every
solution over any $A$-algebra supplies all identities of Steps 4--6. This uses equality of
polynomials, not coefficientwise equality of classes in a quotient. The supports bound the
selected solution and witnesses, and need not parametrize every possible map. Uses:
def-weil-pbc-mv-polynomial-ring.

9. Apply henselian-pair approximation with $I=\mathfrak m$, $N=1$ to the finite system of Step
8. The henselian local hypothesis says that $(A,\mathfrak m)$ is henselian; the G-ring
hypothesis includes that $A$ is Noetherian. The completion is precisely the completion in the
cited approximation theorem. It therefore supplies $z\in A^d$ satisfying every $h_l(z)=0$ with
$\widehat z_l-\iota(z_l)\in\mathfrak m\widehat A$ for every coordinate. In particular this
approximates the coefficients of $F$ together with the idempotent, inverse and
relation-membership witnesses, so all their identities remain exact over $A$. Uses:
def-weil-pbc-henselian-terminology, def-weil-pbc-g-ring,
lem-weil-pbc-henselian-pair-approximation.

10. Decode the solution $z$ by Steps 4--5, now with $R=A$. We obtain an algebra map $f:Q\to P$,
an idempotent $e\in Q$, and an additive multiplicative $A$-linear map $g:P\to Q$ with $g(1)=e$,
$fg=1$ and $gf(q)=eq$. Thus $f$ is surjective. Also $f(e)=1$, so $(1-e)Q\subseteq\ker f$; if
$f(q)=0$ then $eq=gf(q)=0$ and $q=(1-e)q$, proving $\ker f=(1-e)Q$. Consequently $f$ induces an
isomorphism $Q/(1-e)\simeq P$. This deduction does not require $g$ to be a unital map to $Q$.
Uses: def-weil-pbc-algebra-hom-quotient.

11. Let $w=\operatorname{Spec}f:X\to Y$. The three sets of equations of Step 6, which hold over
$A$, say that $w$ preserves all the specified group operations: equality on the algebra
generators implies equality of the corresponding scheme maps. For multiplication the common
source has algebra $P\otimes_AP$, as supplied by the affine-fibre-product theorem; for identity
it is $A$; for inverse it is $P$. Hence $w$ is an $A$-group homomorphism. Uses:
def-weil-affine-spectrum, lem-weil-pbc-fibre-product-affine-spectra,
def-weil-pbc-mv-polynomial-ring.

12. The kernel description identifies $w$ with
$\operatorname{Spec}(Q/(1-e))\to\operatorname{Spec}Q$, which is a closed immersion by the affine
characterization. The elementary idempotent calculation of Step 2 identifies its quotient
algebra, compatibly with the map from $Q$, with $Q_e$. The affine-basic-open theorem identifies
$\operatorname{Spec}Q_e$ with the open subscheme $D(e)$, and the clopen-idempotent theorem says
$D(e)$ is also closed. Thus $w$ is an open immersion as well as a closed immersion. Uses:
def-weil-closed-immersion, def-weil-open-immersion,
lem-weil-pbc-affine-open-section-vanishing-prime, lem-weil-pbc-spec-clopen-idempotent,
def-weil-affine-spectrum.

13. Since $A$ is Noetherian, its maximal ideal is finitely generated. Completion modulo this
ideal is canonically $A/\mathfrak m=k$ by the completion-mod-power theorem with $N=1$. Every
coefficient of $F_j$ from $z$ therefore has the same image in $k$ as the corresponding
coefficient in the chosen representative of $f^{\wedge}(y_j)$. Evaluation gives identical images
of every $y_j$ in $P\otimes_Ak$, so the two $k$-algebra maps $Q\otimes_Ak\to P\otimes_Ak$ are
equal. The affine-spectrum correspondence gives $w_k=v_k$. Only this residue equality follows
from approximation; none of the argument requires equality of the maps over $\widehat A$. Uses:
def-weil-pbc-g-ring, lem-weil-pbc-adic-completion-mod-power, def-weil-pbc-mv-polynomial-ring,
def-weil-affine-spectrum.
-/
theorem exists_clopen_groupHom_of_completion
    (A : Type u) [CommRing A] [HenselianLocalRing A] (hA : IsGRing A)
    (P Q : Type u) [CommRing P] [CommRing Q] [Algebra A P] [Algebra A Q]
    [Algebra.FinitePresentation A P] [Algebra.FinitePresentation A Q]
    [GrpObj ((Spec (.of P)).asOver (Spec (.of A)))]
    [GrpObj ((Spec (.of Q)).asOver (Spec (.of A)))]
    (v : (Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).mapGrp.obj
          (Grp.mk ((Spec (.of P)).asOver (Spec (.of A)))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).mapGrp.obj
          (Grp.mk ((Spec (.of Q)).asOver (Spec (.of A)))))
    (hvOpen : IsOpenImmersion v.hom.hom.left)
    (hvClosed : IsClosedImmersion v.hom.hom.left) :
    ∃ w : Grp.mk ((Spec (.of P)).asOver (Spec (.of A))) ⟶
        Grp.mk ((Spec (.of Q)).asOver (Spec (.of A))),
      IsOpenImmersion w.hom.hom.left ∧ IsClosedImmersion w.hom.hom.left ∧
        (Over.pullback (Spec.map (CommRingCat.ofHom
          (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A)).toRingHom))).mapGrp.map
            ((Over.pullback (Spec.map (CommRingCat.ofHom
              (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).mapGrp.map w) =
        (Over.pullback (Spec.map (CommRingCat.ofHom
          (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A)).toRingHom))).mapGrp.map v := by
  sorry

end AlgebraicGeometry
