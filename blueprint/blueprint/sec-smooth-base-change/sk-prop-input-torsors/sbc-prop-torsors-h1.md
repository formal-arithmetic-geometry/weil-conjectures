+++
id = "sbc-prop-torsors-h1"
kind = "theorem"
title = "Torsors and etale $H^1$"
order = 1409
tags = ["latex:proposition"]
uses = ["def-galois-fibre-functor", "def-weil-pbc-finite-torsors", "lem-fet-galois-category", "lem-galois-axioms", "thm-galois-fundamental", "thm-galois-lc-etale", "thm-galois-torsor-h1"]
+++
Let $Y$ be a scheme and $M$ a finite abelian group. Then there is a
canonical bijection, natural in $(Y,M)$,

$$
\operatorname{Tor}^1(Y,M)\xrightarrow{\ \sim\ }H^1(Y_{\Et},\underline M)
$$

between the pointed set of isomorphism classes of $M$-torsors of
[def-weil-pbc-finite-torsors] and $H^1(Y_{\Et},\underline M)$, and an
$M$-torsor is the same thing as a finite etale $Y$-scheme with a simply
transitive $M$-action. Moreover, let $Y$ be connected
with geometric point $\bar y$. For an $M$-torsor $P$, viewed as a finite
etale $Y$-scheme, and $p\in|P_{\bar y}|$, let
$f_P:\pi_1(Y,\bar y)\to M$ be defined by $g\cdot p=p+f_P(g)$; it is
a continuous homomorphism independent of $p$ and of $P$ within its
isomorphism class. Then $P$ is connected — that is, a Galois cover with
group $M$ — exactly when $f_P$ is surjective (the case of the sketch is
$M=\Z/d\Z$).
(Stacks 02NE, together with the finite-etale correspondence; cf. Milne,
*Lectures on Etale Cohomology*, III.3.)

## Proof

The bijection, with its naturality, is [thm-galois-torsor-h1]. By
[thm-galois-lc-etale] the functor
$P\mapsto\underline{\operatorname{Hom}}_Y(-,P)$ is an equivalence from
finite etale $Y$-schemes to finite locally constant sheaves which carries
simply transitive $M$-actions to simply transitive ones, and conversely;
since an $M$-torsor is by [def-weil-pbc-finite-torsors] a finite locally
constant sheaf with an $M$-action for which $M\times P\to P\times_YP$ is
an isomorphism, $M$-torsors are the same as finite etale $Y$-schemes with
a simply transitive $M$-action.

Now let $Y$ be connected and $P$ an $M$-torsor, viewed as a
finite etale $Y$-scheme with $M$ acting by $Y$-automorphisms. By
[thm-galois-fundamental] the fibre functor $F_{\bar y}$ of
[def-galois-fibre-functor] identifies $P$ with the finite continuous
$\pi_1(Y,\bar y)$-set $|P_{\bar y}|$, and the $M$-action with an action
of $M$ on $|P_{\bar y}|$ by $\pi_1$-equivariant maps; this action is
simply transitive because the isomorphism $M\times P\to P\times_YP$
becomes $M\times|P_{\bar y}|\cong|P_{\bar y}|\times|P_{\bar y}|$ under
the exact functor $F_{\bar y}$. In particular $|P_{\bar y}|\neq\emptyset$.

*The homomorphism.* Fix $p\in|P_{\bar y}|$. By simple transitivity there
is a unique $f_P(g)\in M$ with $g\cdot p=p+f_P(g)$. As the two actions
commute,
$gh\cdot p=g\cdot(p+f_P(h))=(g\cdot p)+f_P(h)=p+f_P(g)+f_P(h)$, so
$f_P$ is a homomorphism. It is continuous: for $m\in M$ the set
$\{g:f_P(g)=m\}$ is the stabilizer-coset $\{g:g\cdot p=p+m\}$, which
is open because the action on the finite discrete set $|P_{\bar y}|$ is
continuous (the definition of a $\pi_1(Y,\bar y)$-set in
[def-galois-fibre-functor]). Replacing $p$ by $p+a$ gives
$g\cdot(p+a)=p+a+f_P(g)$, so $f_P$ does not depend on $p$, $M$ being
abelian; and an $M$-equivariant isomorphism $P\cong P'$ carries $p$ to a
point $p'$ with the same $f$, so $f_P$ only depends on the class of $P$,
hence (by the bijection) on the class in $H^1(Y_{\Et},\underline M)$.

*Connectedness.* By [lem-fet-galois-category], $\mathrm{F\acute Et}(Y)$
with $F_{\bar y}$ is a Galois category whose connected objects are the
connected finite etale $Y$-schemes, and the equivalence of
[thm-galois-fundamental] preserves finite coproducts and initial
objects, so $P$ is connected exactly when the nonempty
$\pi_1(Y,\bar y)$-set $|P_{\bar y}|$ is not a disjoint union of two
nonempty sub-$\pi_1$-sets, i.e. exactly when $\pi_1(Y,\bar y)$ acts
transitively on it (each orbit is a sub-$\pi_1$-set with an invariant
complement). Since $p\mapsto p+m$ is a bijection $M\to|P_{\bar y}|$
and the orbit of $p$ is $p+f_P(\pi_1(Y,\bar y))$, the action is
transitive exactly when $f_P$ is surjective.

*Galois.* If $P$ is connected, $M$ acts on $P$ by
$Y$-automorphisms, faithfully and transitively on the fibre
$|P_{\bar y}|$ of cardinality $\#M$, so $\#\operatorname{Aut}(P)\ge\#M$;
by [lem-galois-axioms] (6) $\#\operatorname{Aut}(P)\le\#|P_{\bar y}|=\#M$.
Hence $\operatorname{Aut}(P)=M$ acts simply transitively on the
fibre, and $P$ is a Galois cover with group $M$. Conversely a
Galois cover is connected by definition.
