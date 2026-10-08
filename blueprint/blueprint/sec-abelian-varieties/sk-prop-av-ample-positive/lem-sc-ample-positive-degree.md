+++
id = "lem-sc-ample-positive-degree"
kind = "lemma"
title = "Ample modules on proper curves have positive degree"
lean = ["AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple"]
order = 550
uses = ["def-sc-ample", "def-sc-curves", "def-sc-hilbert-degree", "lem-sc-hilbert-polynomial"]
+++
Let $k$ be algebraically closed, $C$ a proper curve over $k$ of
dimension one (in the sense of [def-sc-curves]; $C$ need not be
connected and may have zero-dimensional connected components), and
$\mathcal L$ an ample invertible $\mathcal O_C$-module
([def-sc-ample]). Then $\deg\mathcal L>0$, where
$\deg\mathcal L:=\deg_{\mathcal L}(C)$ is the degree of
[def-sc-hilbert-degree], i.e. the coefficient of $m$ in the Hilbert
polynomial $m\mapsto\chi(C,\mathcal L^{\otimes m})$ of
[lem-sc-hilbert-polynomial]. In particular $\mathcal L$ is not
trivial. (For a connected curve this is *Stacks Project, Varieties,
Lemma 33.44.14, [Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X).*)

(The hypothesis $\dim C=1$ cannot be dropped: on a proper curve
$C=\operatorname{Spec}k$ of dimension zero every invertible module,
ample or not, is trivial and $\chi(C,\mathcal L^{\otimes m})=1$ for all
$m$, so the coefficient of $m$ is $0$; note that the Hilbert degree
$\deg_{\mathcal L}(C)$ of [def-sc-hilbert-degree] is then $0!\cdot1=1$,
since in dimension $g=0$ the leading coefficient is the constant term.
The two numbers agree only when $\dim C=1$, which is the case the lemma
is about.)

## Proof

*The connected case.* If $C$ is a connected curve (nonempty, connected,
of dimension one), this is the recorded classical input of the
statement, Stacks Project, Varieties, Lemma 33.44.14
([Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)): on a proper
curve an ample invertible module has positive degree
$\deg\mathcal L=\chi(C,\mathcal L)-\chi(C,\mathcal O_C)$. By
Riemann–Roch on a proper curve (Stacks Project, Varieties, Section
33.44, Degrees on curves) one has
$\chi(C,\mathcal L^{\otimes m})=m\deg\mathcal L+\chi(C,\mathcal O_C)$
for all $m\in\mathbf Z$, so $\deg\mathcal L$ is exactly the coefficient
of $m$ in the Hilbert polynomial, i.e. $\deg_{\mathcal L}(C)$ of
[def-sc-hilbert-degree] with $g=1$. No separate proof of this case is
given.

*The general case.* Since $C$ is of finite type over $k$ it is
noetherian, so it has finitely many connected components
$C_1,\dots,C_r$, each open and closed in $C$, and
$C=C_1\sqcup\dots\sqcup C_r$. Cohomology of a disjoint union is the
direct sum of the cohomologies of the pieces, hence for every $m$
$$
\chi(C,\mathcal L^{\otimes m})=\sum_{i=1}^r\chi(C_i,\mathcal L^{\otimes m}|_{C_i}).
$$
Each $C_i$ is a proper curve over $k$ (a closed subscheme of $C$), and
$\mathcal L|_{C_i}$ is ample, since the restriction of an ample
invertible module to a closed subscheme is ample (if
$\mathcal L^{\otimes n}$ is the pullback of $\mathcal O(1)$ along a
closed immersion $C\hookrightarrow\mathbf P^N_k$, then
$\mathcal L^{\otimes n}|_{C_i}$ is its pullback along the composite
closed immersion $C_i\hookrightarrow\mathbf P^N_k$; Stacks Project,
Properties of Schemes, Section 28.26).

If $\dim C_i=0$, then $C_i$ is connected, finite over $k$, hence
$C_i=\operatorname{Spec}A_i$ for an artinian local $k$-algebra $A_i$ of
finite dimension; every invertible module on the spectrum of a local
ring is trivial, so $\chi(C_i,\mathcal L^{\otimes m}|_{C_i})
=\dim_kH^0(C_i,\mathcal O_{C_i})=\dim_kA_i$ is independent of $m$, and
its coefficient of $m$ is $0$.

If $\dim C_i=1$, then $C_i$ is a connected curve in the sense of
[def-sc-curves], and by the connected case the coefficient of $m$ in
$\chi(C_i,\mathcal L^{\otimes m}|_{C_i})$ is
$\deg(\mathcal L|_{C_i})>0$.

Since $\dim C=1$, at least one component $C_i$ has dimension one.
Therefore the coefficient of $m$ in $\chi(C,\mathcal L^{\otimes m})$ is
$\sum_{\dim C_i=1}\deg(\mathcal L|_{C_i})>0$; in particular the Hilbert
polynomial of [lem-sc-hilbert-polynomial] has degree exactly $g=1$ and
$\deg\mathcal L=\deg_{\mathcal L}(C)=1!\cdot(\text{this coefficient})>0$.
Finally, if $\mathcal L\cong\mathcal O_C$ then
$\chi(C,\mathcal L^{\otimes m})=\chi(C,\mathcal O_C)$ is constant in
$m$, whose coefficient of $m$ is $0$; so $\mathcal L$ is not trivial.
