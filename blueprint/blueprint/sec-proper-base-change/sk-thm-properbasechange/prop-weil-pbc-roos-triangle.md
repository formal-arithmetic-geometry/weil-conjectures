+++
id = "prop-weil-pbc-roos-triangle"
kind = "theorem"
title = "Roos triangle and Milnor exact sequence"
order = 1246
uses = ["def-weil-derived-limit", "def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-derived-inverse-limit", "lem-weil-derived-limit-existence", "prop-weil-pbc-derived-product-representation"]
tags = ["latex:proposition"]
+++
For every $M_\bullet\in D(\operatorname{Tow}_{A}(T))$, the tower category
being that of [def-weil-pbc-adic-coefficient-datum], the transition maps
define an endomorphism $s$ of $R\!\prod_nM_n$, and the defining Roos triangle
of [def-weil-pbc-derived-inverse-limit] is the functorial distinguished
triangle

$$
 \Rlim M_\bullet\longrightarrow R\!\prod_nM_n
 \xrightarrow{1-s}R\!\prod_nM_n
 \longrightarrow(\Rlim M_\bullet)[1].
$$

If $U$ is a weakly contractible quasi-compact object of $T_{\Proet}$, then
for every $i\in\mathbf Z$ this triangle induces the functorial exact sequence

$$
 0\to\varprojlim{}^1_nH^{i-1}(U,M_n)
 \to H^i(U,\Rlim M_\bullet)
 \to\varprojlim_nH^i(U,M_n)\to0.
$$

(*Source note:* the canonical triangle is Stacks Project, More on Algebra,
Lemma 15.88.9 (Tag [07KX](https://stacks.math.columbia.edu/tag/07KX)): for
$K=(K_n^\bullet)$ in $D(\textit{Ab}(\mathbf N))$ there is a canonical
distinguished triangle $R\lim K\to\prod_nK_n^\bullet\to\prod_nK_n^\bullet\to
R\lim K[1]$, so that $R\lim K$ is a derived limit in the sense of Definition
13.34.1 (Tag [08TC](https://stacks.math.columbia.edu/tag/08TC)); the
associated short exact sequences are Lemma 15.88.10 (Tag
[07KY](https://stacks.math.columbia.edu/tag/07KY): the long exact cohomology
sequence breaks up into $0\to R^1\lim_nH^{p-1}(K_n^\bullet)\to H^p(R\lim
K)\to\lim_nH^p(K_n^\bullet)\to0$), and the representation of $\Rlim$ by the
two-term complex $\prod A_n\to\prod A_n$, $(x_n)\mapsto(x_n-f_{n+1}(x_{n+1}))$,
in degrees $0,1$, together with $R^p\lim A_n=0$ for $p>1$, is Lemma 15.88.1
(Tag [07KW](https://stacks.math.columbia.edu/tag/07KW)). The Stacks entries
are stated for towers of abelian groups; the blueprint states the same
triangle for the tower category $\operatorname{Tow}_A(T)$ over $T_{\Proet}$
with $A_T$-coefficients, where the two derived products are those of
[prop-weil-pbc-derived-product-representation], and it evaluates the Milnor
sequence at a weakly contractible quasi-compact $U\in T_{\Proet}$, which is
the form in which it is used below.)

## Proof

The triangle is the definition of $\Rlim$ in
[def-weil-pbc-derived-inverse-limit], namely the defining Roos triangle for
the system $(\operatorname{ev}_nM_\bullet)$, with the endomorphism $1-s$
induced by the transition maps; the identification of its middle term with
$R\!\prod_nM_n$ is the representability statement of the derived-limit
existence lemma. For the exact sequence the functor $\varprojlim$ is the
kernel of $1-s$ on the product; the cokernel of $1-s$ is the *first derived
limit* $\varprojlim^1M_n$, an exact-in-general cokernel, so the ordinary
sequence

$$
 0\to\varprojlim_nM_n\to\prod_nM_n
 \xrightarrow{1-s}\prod_nM_n\to\varprojlim^1_nM_n\to0
$$

is exact (the left exactness of $\varprojlim$ with the cokernel
$\varprojlim^1$ recorded rather than zero) in the evaluation categories of
[def-weil-pbc-adic-coefficient-datum]. This exhibits $\varprojlim$ as the
kernel of $1-s$ and $\varprojlim^1$ as its cokernel; the *Roos resolution* is
the two-term complex

$$
 \prod_nM_n\xrightarrow{\ 1-s\ }\prod_nM_n
$$

placed in degrees $0,1$, whose cohomology is $\varprojlim$ in degree $0$ and
$\varprojlim^1$ in degree $1$ — and whose higher cohomology vanishes because,
for a tower of module sheaves, the higher derived limits $\varprojlim^i$
vanish for $i\geq2$ (the Roos/Mittag-Leffler chain: $\varprojlim^1$ of a
countable tower of modules is computed by the cokernel of $1-s$, and
$\varprojlim^i=0$ for $i\geq2$; this is the classical Milnor exact sequence
of Stacks Project, More on Algebra, Lemma 15.88.1, Tag
[07KW](https://stacks.math.columbia.edu/tag/07KW), which represents $\Rlim$
by the two-term complex $\prod\to\prod$ sitting in degrees $0,1$, and the
resulting derived-limit triangle of Lemma 15.88.9, Tag
[07KX](https://stacks.math.columbia.edu/tag/07KX), with the short exact
sequences of Lemma 15.88.10, Tag
[07KY](https://stacks.math.columbia.edu/tag/07KY)); that triangle is exactly
the triangle displayed in the statement. For a weakly contractible
quasi-compact $U\in T_{\Proet}$, the functor $\Gamma(U,-)$ is exact on
$\Mod(T_{\Proet},A_T)$, preserves the products and limits involved and the
maps $1-s$, so the long exact cohomology sequence of the triangle is the
displayed functorial exact sequence, with $\varprojlim{}^1$ arising as the
cohomology of $1-s$ in the degree below.
