+++
id = "sk-prop-divisor-gen"
kind = "section"
title = "Divisor sequence"
order = 897
uses = ["sk-def-curve"]
lean = ["AlgebraicGeometry.Scheme.exists_shortExact_divisorSequence"]
+++
*Proposition (sketch).*

Let $X$ be an integral regular noetherian scheme (e.g. a smooth
variety over a field) with generic point $\eta$, $i:\eta\to X$, and
let $X^{(1)}$ be the set of codimension-$1$ points of $X$. There is
an exact sequence of étale sheaves on $X$

$$
0\longrightarrow\mathbb G_m\longrightarrow i_*\mathbb G_{m,\eta}
\xrightarrow{\ \operatorname{div}\ }
\bigoplus_{x\in X^{(1)}}i_{x*}\Z\longrightarrow0 .
$$

The divisor map sends a rational function to
$\sum_{x\in X^{(1)}}\operatorname{ord}_x(\cdot)[x]$.

## Proof

*Curve case.* Exactness is checked on stalks at geometric points.
At the generic point both outer terms are as required. At a closed
point the strictly henselian local ring is a discrete valuation ring
$R$ ($C$ regular of dimension $1$) with fraction field $K$, and the
sequence of stalks is
$1\to R^\times\to K^\times\xrightarrow{\operatorname{ord}}\Z\to0$,
which is exact by the definition of a discrete valuation: a
rational function is a unit exactly when its order vanishes, and
$\operatorname{ord}$ is surjective because a uniformiser exists.
This is the structure of meromorphic functions on a curve (poles
with multiplicities), stated stalkwise.

*General case.* Again exactness is stalkwise, with the preceding
curve calculation providing the one-dimensional local input.
Concretely, at a geometric point $\bar x$ the local
ring $A=\mathcal O^{\mathrm{sh}}_{X,\bar x}$ is a regular local
ring, hence a noetherian normal domain, so $A$ is the intersection
of the discrete valuation rings $A_{\mathfrak p}$ over the height-one
primes $\mathfrak p$ (Krull / Serre's criterion, ``algebraic Hartogs'':
a rational function regular in codimension $1$ is regular). This is
exactly left exactness and exactness in the middle. Surjectivity on
the right is local and involves only finitely many height-one primes
at a time, so for each $\mathfrak p$ it is the preceding curve case
applied to $\Spec A_{\mathfrak p}$, whose
uniformiser supplies the required rational function; the direct sum
(not product) is what makes the local finiteness usable.

Uses: [sk-def-curve]
