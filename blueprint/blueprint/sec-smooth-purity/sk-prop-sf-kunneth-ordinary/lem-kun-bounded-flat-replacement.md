+++
id = "lem-kun-bounded-flat-replacement"
kind = "lemma"
title = "Functorial bounded-above flat replacement"
order = 1722
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-etale-sheaves"]
+++
There is a construction which assigns to every bounded-above complex
$\mathcal F^\bullet$ of $\Lambda_T$-module sheaves together with an
integer $N$ such that $\mathcal F^i=0$ for $i>N$ a bounded-above
complex $\Phi(\mathcal F)^\bullet$ of flat $\Lambda_T$-module
sheaves with $\Phi(\mathcal F)^i=0$ for $i>N$ and a termwise
surjective quasi-isomorphism
$\Phi(\mathcal F)^\bullet\to\mathcal F^\bullet$; the construction is
functorial, in the sense that a map
$\mathcal F^\bullet\to\mathcal G^\bullet$ between complexes which both
vanish above $N$ induces a map
$\Phi(\mathcal F)^\bullet\to\Phi(\mathcal G)^\bullet$ compatible with
the two quasi-isomorphisms. In particular every bounded-above complex
of $\kunZn$-module sheaves on $T_{\Et}$ is quasi-isomorphic to a
bounded-above complex of flat sheaves.

## Proof

For a $\Lambda_T$-module sheaf $F$ in the sense of
[def-weil-pbc-etale-sheaves] let $\operatorname{Free}(F)$ be the
sheafification of the presheaf $U\mapsto\Lambda_T^{(F(U))}$ of free
$\Lambda_T$-modules on the sections of $F$. Evaluation of basis
elements is a canonical epimorphism
$\operatorname{Free}(F)\twoheadrightarrow F$; the construction is
functorial; and $\operatorname{Free}(F)$ is flat, because its stalks
are free $\Lambda$-modules. Given $\mathcal F^\bullet$ with
$\mathcal F^i=0$ for $i>N$, set
$\Phi^N=\operatorname{Free}(\mathcal F^N)$ and, descending
inductively, let

$$
P^i=\mathcal F^i\times_{\mathcal F^{i+1}}\Phi^{i+1}
$$

be the fibre product of $d^i:\mathcal F^i\to\mathcal F^{i+1}$ and
$\Phi^{i+1}\to\mathcal F^{i+1}$, set
$\Phi^i=\operatorname{Free}(P^i)$, let
$\Phi^i\to\Phi^{i+1}$ be the composite
$\Phi^i\twoheadrightarrow P^i\to\Phi^{i+1}$, and let
$\Phi^i\to\mathcal F^i$ be the composite
$\Phi^i\twoheadrightarrow P^i\to\mathcal F^i$. The squares commute by
the definition of the fibre product, and
$\Phi^i\twoheadrightarrow\mathcal F^i$ is an epimorphism because
$P^i\twoheadrightarrow\mathcal F^i$ is: for $i<N$ this follows from
the surjectivity of $\Phi^{i+1}\twoheadrightarrow\mathcal F^{i+1}$,
and for $i\ge N$ both differentials out of $\mathcal F^i$ vanish, so
that $P^i\cong\mathcal F^i$. Every step is functorial, which gives
the asserted compatibility. Finally $\Phi^\bullet\to\mathcal F^\bullet$ is a quasi-isomorphism: its kernel
$\mathcal K^\bullet$, with
$\mathcal K^i=\ker(\Phi^i\to\mathcal F^i)$, has surjective
differentials $\mathcal K^i\twoheadrightarrow\mathcal K^{i+1}$, since a
preimage of $\kappa\in\mathcal K^{i+1}$ is any lift of
$(0,\kappa)\in P^i$ under $\Phi^i\twoheadrightarrow P^i$; hence

$$
\mathcal H^i(\mathcal K)
=\ker(d^i)/\operatorname{im}(d^{i-1})
=\ker(d^i)/\mathcal K^i=0
$$

for every $i$, the case $i=N$ being the same computation with
$\mathcal K^{N+1}=0$ and $\operatorname{im}(d^{N-1})=\mathcal K^N$.
A termwise surjective map of complexes with acyclic kernel is a
quasi-isomorphism, by the long exact cohomology sequence of
$0\to\mathcal K^\bullet\to\Phi^\bullet\to\mathcal F^\bullet\to0$ and
the definition of the derived category in
[def-weil-pbc-derived-categories].
