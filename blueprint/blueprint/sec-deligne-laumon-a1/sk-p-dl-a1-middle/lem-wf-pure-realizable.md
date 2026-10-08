+++
id = "lem-wf-pure-realizable"
kind = "lemma"
title = "A pure sheaf is realizable"
order = 2751
uses = ["def-weil-punctual-weights", "def-wf-constant-weil-twist", "def-wf-iota-real"]
+++
Let $\mathcal F$ be a lisse Weil sheaf which is punctually
$\iota$-pure of weight $w$. Relative to the fixed isomorphism
$\iota$, put $c=\iota^{-1}(q^{w})$ and

$$
\mathcal R(\mathcal F)=\mathcal F\oplus
\bigl(\mathcal F^\vee\otimes\mathcal B_c\bigr),
$$

the second summand being the constant
Weil twist of the linear dual.
Then $\mathcal R(\mathcal F)$ is $\iota$-real in the sense of
[def-wf-iota-real]; consequently $\mathcal F$ is
$\iota$-realizable.

## Proof

At a closed point $y$ of degree $m$, let $\alpha$ be a Frobenius
eigenvalue of $\mathcal F$. Purity of weight $w$ in
[def-weil-punctual-weights] gives
$|\iota(\alpha)|^2=q^{mw}=q_y^{w}$. The corresponding eigenvalue of
the second summand is $c^m\alpha^{-1}$ by
[def-wf-constant-weil-twist], and hence

$$
\iota\bigl(c^m\alpha^{-1}\bigr)
=\frac{q^{mw}}{\iota(\alpha)}
=\overline{\iota(\alpha)},
$$

because $q^{mw}=|\iota(\alpha)|^2=\iota(\alpha)\overline{\iota(\alpha)}$.
Since this holds for every eigenvalue and every degree, and is
involutionary, the local eigenvalue multiset of $\mathcal R(\mathcal F)$
is conjugation-stable at every closed point; by
[def-wf-iota-real] the sheaf $\mathcal R(\mathcal F)$ is
$\iota$-real. The
projection onto the first summand gives the realizability of
$\mathcal F$.
