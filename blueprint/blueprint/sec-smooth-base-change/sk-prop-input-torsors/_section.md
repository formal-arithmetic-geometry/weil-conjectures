+++
id = "sk-prop-input-torsors"
kind = "section"
title = "Torsors and étale $H^1$"
order = 1406
uses = ["sk-def-smooth"]
lean = ["AlgebraicGeometry.Scheme.EtaleTorsor", "AlgebraicGeometry.Scheme.EtaleTorsor.exists_quotientEquivSheafH"]
+++
*Proposition (sketch).*

Let $Y$ be a scheme and $M$ a finite abelian group. Then there is a
canonical bijection, natural in $(Y,M)$,

$$
\mathrm{Tor}^1(Y,M)\xrightarrow{\ \sim\ }H^1(Y_{\Et},\underline M)
$$

between the isomorphism classes of $M$-torsors on $Y_{\Et}$ and
$H^1(Y_{\Et},\underline M)$, and an $M$-torsor is the same thing as a
finite étale $Y$-scheme with a simply transitive $M$-action. For
$M=\Z/d\Z$ and $Y$ connected with geometric point $\bar y$, the
torsor attached to a class is connected — that is, a Galois cover
with group $\Z/d\Z$, the input taken by [sk-prop-input-spreading]
— exactly when the corresponding continuous homomorphism
$\pi_1(Y,\bar y)\to\Z/d\Z$ is surjective.
(02NE, together with the finite-étale correspondence;
cf. Milne, *Lectures on Étale Cohomology*, III.3.)
The sketch below condenses the proofs of the detailed blueprint,
Ch. 02b.

## Proof

*A flasque embedding.* For a sheaf $\mathcal G$ on $Y_{\Et}$
the Godement sheaf $G(\mathcal G)(U)=\prod_{u\in U}\mathcal G_u$
contains $\mathcal G$ and is flasque, its restriction maps only
discarding coordinates. A flasque sheaf is acyclic: in
$0\to\mathcal A\to\mathcal B\to\mathcal C\to0$ with $\mathcal A$
flasque, local liftings of a section of $\mathcal C$ patch, so global
sections are right exact on such sequences and dimension shifting
gives $H^q(\mathcal A)=0$ for $q\ge1$. Put $I=G(\underline M)$ and
$J=I/\underline M$, so that
$0\to\underline M\to I\xrightarrow{d}J\to0$ is exact with $I$
acyclic; the long exact sequence gives
$H^1(Y_{\Et},\underline M)=\operatorname{coker}(d_Y)$. (Only the
acyclicity of $I$ is used: $J$ is not acyclic in general, since
$H^a(J)=H^{a+1}(\underline M)$ for $a\ge1$, which is nonzero e.g. for
$\Z/\ell$ on $\Pone$ over an algebraically closed field.)

*From a class to a torsor.* For $s\in J(Y)$ put
$P_s(U)=\{x\in I(U):d(x)=s|_U\}$, with $M$ acting by translation.
Two lifts of $s$ differ by a section of $\ker d=\underline M$, so the
action is simply transitive; $P_s$ is locally nonempty because $J$ is
the quotient sheaf of $I$, and over a cover trivializing it
$P_s\cong\underline M$. So $P_s$ is an $M$-torsor. Translation by
$x\in I(Y)$ gives $P_{s+d(x)}\cong P_s$, so $s\mapsto[P_s]$ is
defined on $\operatorname{coker}(d_Y)$, and functoriality of
$I,J,d$ and of pullback makes it natural in $(Y,M)$.

*Injectivity.* An isomorphism $P_s\cong P_{s'}$ is, over a
cover trivializing both by sections $p_i,p_i'$, translation by
$a_i=p_i'-p_i\in I(U_i)$. Compatibility with the torsor structures
says exactly that the $a_i$ agree on overlaps, so they glue to $a\in I(Y)$ with $d(a)=s'-s$, i.e. $s$ and $s'$ have the same class.

*Surjectivity.* Trivialize an $M$-torsor $P$ over a cover
$\{U_i\to Y\}$ by sections $p_i$ and put
$c_{ij}=p_i-p_j\in\underline M(U_{ij})$, a Čech $1$-cocycle. The
Čech complex of the Godement sheaf $I$ with respect to any
covering is acyclic in positive degrees (at each geometric point it
is the cochain complex of the nerve of a surjection of sets, which is
contractible), so $c_{ij}=a_i|_{U_{ij}}-a_j|_{U_{ij}}$ with
$a_i\in I(U_i)$; the sections $d(a_i)\in J(U_i)$ agree on overlaps
and glue to $s\in J(Y)$. Then $a_i\in P_s(U_i)$ trivialize $P_s$
with the same cocycle $(c_{ij})$, so $P$ and $P_s$ are glued from the
same trivial torsors by the same transition data, and $P\cong P_s$.

*Torsors are finite étale covers.* The functor
$P\mapsto\underline{\operatorname{Hom}}_Y(-,P)$ from finite étale
$Y$-schemes to finite locally constant sheaves is an equivalence: a
finite étale cover is trivialized by a surjective étale base
change, which makes the sheaf locally constant, and effective étale
descent for finite étale morphisms produces the inverse. It is
compatible with base change and carries simply transitive
$M$-actions to simply transitive ones, so an $M$-torsor sheaf is
represented by a finite étale $Y$-scheme with a simply transitive
$M$-action, and conversely.

*Connectedness.* Let $Y$ be connected. Under the fibre-functor
equivalence a torsor $P$ is a finite continuous
$\pi_1(Y,\bar y)$-set whose $M$-action is simply transitive and
commutes with the $\pi_1$-action; choosing $p\in P_{\bar y}$ there is
a unique $f_P(g)\in M$ with $g\cdot p=p+f_P(g)$, and commutation
makes $f_P$ a homomorphism, continuous because $g\mapsto g\cdot p$ is
continuous into the finite discrete $P_{\bar y}$. Since $M$ is
abelian, $f_P$ does not depend on $p$. Now $P$ is connected exactly
when $\pi_1(Y,\bar y)$ acts transitively on $P_{\bar y}$, i.e. when
$f_P$ is surjective; for $M=\Z/d\Z$ a surjective $f_P$ is a connected
finite étale cover whose automorphism group $\Z/d\Z$ acts simply
transitively on the fibre, that is, a Galois cover with group
$\Z/d\Z$.

*Scope of the Lean statement.* The bijection is stated together with
the one further property that [sk-thm-vanishing] uses, namely that the
class of a torsor vanishes exactly when its structure morphism admits
a section. Its naturality in $Y$ is not stated: expressing it needs a
pullback map $H^1(Y_{\Et},M)\to H^1(Y'_{\Et},M)$ on sheaf cohomology
along a morphism of schemes, which is not yet available. The
connectedness criterion above, which needs the étale fundamental
group, is likewise left to the prose.

Uses: `cor-galois-abelian-h1`, [sk-def-smooth], `thm-galois-lc-etale`, `thm-galois-torsor-h1`
