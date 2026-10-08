+++
id = "cor-galois-abelian-h1"
kind = "theorem"
title = "Abelian case: torsors, characters and $H^1$"
order = 2581
uses = ["def-galois-fibre-functor", "def-weil-pbc-finite-torsors", "lem-galois-axioms", "thm-galois-fundamental", "sbc-prop-torsors-h1", "thm-galois-torsor-h1"]
tags = ["latex:corollary"]
+++
Let $Y$ be connected with geometric point $\bar y$ and let $M$ be a
finite abelian group. Then there is a canonical bijection

$$
H^1(Y_{\Et},\underline M)\xrightarrow{\ \sim\ }
\operatorname{Hom}_{\mathrm{cont}}\bigl(\pi_1(Y,\bar y),M\bigr),
$$

given on torsors by choosing $p\in P_{\bar y}$ — a simply transitive
$M$-set — and sending $P$ to the continuous homomorphism $f_P$ with

$$
g\cdot p=p+f_P(g)\qquad(g\in\pi_1(Y,\bar y));
$$

the class of $P$ is independent of the choice of $p$ because $M$ is
abelian. (This is the identification used, without citation, in the proof
of the additive-character lemma of the monodromy chapter.)

## Proof

By [thm-galois-fundamental] an $M$-torsor $P$ in the sense of
[def-weil-pbc-finite-torsors] is a finite
$\pi_1$-set with a simply transitive $M$-action commuting with the
$\pi_1$-action. For $p\in P_{\bar y}$, [sbc-prop-torsors-h1] shows that
$g\cdot p=p+f_P(g)$ defines a continuous homomorphism
$f_P:\pi_1(Y,\bar y)\to M$ that is independent of $p$ (as $M$ is abelian)
and depends only on the isomorphism class of $P$.
Conversely a continuous homomorphism $f$ makes $M$ into a finite
continuous $\pi_1$-set by $g\cdot a=f(g)+a$, commuting with
translations, hence corresponds to an $M$-torsor. The constructions are
inverse. The identification with $H^1$ is
[thm-galois-torsor-h1].
