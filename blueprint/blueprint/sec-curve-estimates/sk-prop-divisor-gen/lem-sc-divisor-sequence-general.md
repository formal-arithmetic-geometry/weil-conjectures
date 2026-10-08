+++
id = "lem-sc-divisor-sequence-general"
kind = "lemma"
title = "The divisor sequence of an integral regular scheme"
order = 898
uses = ["lem-sc-regular-dim1-dvr"]
lean = ["AlgebraicGeometry.Scheme.exists_shortExact_divisorSequence"]
+++
Let $X$ be an integral regular noetherian scheme (for example a
connected smooth scheme over a field) with generic point
$j:\eta=\operatorname{Spec}k(X)\to X$, let $X^{(1)}$ be the set of
codimension-one points of $X$, and for $x\in X^{(1)}$ let
$i_x:\operatorname{Spec}k(x)\to X$ be the canonical morphism (not a
closed immersion unless $x$ is closed). The sequence of etale sheaves
on $X$

$$
0\longrightarrow\mathbf G_m\longrightarrow j_*\mathbf G_{m,\eta}
\xrightarrow{\ \operatorname{div}\ }\bigoplus_{x\in X^{(1)}}i_{x*}\mathbf Z\longrightarrow0
$$

is exact, where the first map is the unit
$\mathbf G_m\to j_*j^*\mathbf G_m$ and $\operatorname{div}$ sends a
rational function $f$ to $\sum_{x\in X^{(1)}}\operatorname{ord}_x(f)[x]$.

## Proof

Exactness is checked on stalks at geometric points $\bar x\to X$ lying
over $x\in X$. Let $\mathcal O=\mathcal O_{X,x}$, $K=k(X)$ its fraction
field, and $A=\mathcal O^{sh}_{X,\bar x}$ the strict henselization. Then
$A$ is a regular local ring (the strict henselization of a noetherian
local ring is noetherian, and it is regular iff the original ring is:
*reference: Stacks Project, More on Algebra, henselization and
strict henselization of regular rings*), hence a noetherian normal
domain and a unique factorization domain (Auslander–Buchsbaum:
*reference: Stacks Project, Algebra, regular local rings are
UFDs*). The map $\mathcal O\to A$ is flat and injective. The stalks
are:

- $(\mathbf G_m)_{\bar x}=A^\times$;
- $(j_*\mathbf G_{m,\eta})_{\bar x}=\Gamma(\operatorname{Spec}A\times_X\eta,\mathbf G_m)=(S^{-1}A)^\times$ with $S=\mathcal O\smallsetminus\{0\}$
  (the stalk of a direct image along the quasi-compact quasi-separated
  morphism $j$ is the value on the base change to
  $\operatorname{Spec}A$, and $A\otimes_{\mathcal O}K=S^{-1}A$);
- $(\bigoplus_xi_{x*}\mathbf Z)_{\bar x}=\bigoplus_{\mathfrak q}\mathbf Z$,
  the sum over the points of $\operatorname{Spec}A$ lying over some
  $x'\in X^{(1)}$, i.e. over the primes $\mathfrak q\subset A$ with
  $\mathfrak q\cap\mathcal O$ of height one. These are exactly the
  height-one primes $\mathfrak q$ of $A$ with $\mathfrak q\cap S\neq\emptyset$:
  by flatness (going down) $\operatorname{ht}(\mathfrak q\cap\mathcal O)\le\operatorname{ht}\mathfrak q$,
  and the fibres of $\operatorname{Spec}A\to\operatorname{Spec}\mathcal O$
  are zero-dimensional (each is a filtered limit of the finite
  discrete fibres of etale maps), so
  $\operatorname{ht}\mathfrak q=\operatorname{ht}(\mathfrak q\cap\mathcal O)$
  by the dimension formula for flat local homomorphisms.

For a height-one prime $\mathfrak q$ of $A$ the localization
$A_{\mathfrak q}$ is a regular local ring of dimension one, hence a
discrete valuation ring by [lem-sc-regular-dim1-dvr]; write
$\operatorname{ord}_{\mathfrak q}$ for its normalized valuation. If
$\mathfrak p=\mathfrak q\cap\mathcal O$ corresponds to $x'\in X^{(1)}$,
then $\mathcal O_{\mathfrak p}=\mathcal O_{X,x'}\to A_{\mathfrak q}$ is a
local homomorphism of discrete valuation rings with
$\mathfrak pA_{\mathfrak q}=\mathfrak qA_{\mathfrak q}$ ($A$ is a
filtered colimit of etale, hence unramified, $\mathcal O$-algebras), so
a uniformizer of $\mathcal O_{X,x'}$ stays a uniformizer and
$\operatorname{ord}_{\mathfrak q}$ restricts to $\operatorname{ord}_{x'}$
on $K^\times$. Hence the map $\operatorname{div}$ on stalks is
$f\mapsto(\operatorname{ord}_{\mathfrak q}f)_{\mathfrak q}$; only
finitely many $\operatorname{ord}_{\mathfrak q}f$ are nonzero since $A$
is noetherian.

Injectivity of $A^\times\to(S^{-1}A)^\times$ is clear ($A$ is a
domain). *Exactness in the middle:* units have order zero
everywhere; conversely, if $f\in(S^{-1}A)^\times$ has
$\operatorname{ord}_{\mathfrak q}f=0$ for all $\mathfrak q$ meeting
$S$, then also $\operatorname{ord}_{\mathfrak q}f=0$ for the
height-one primes $\mathfrak q$ with $\mathfrak q\cap S=\emptyset$
(for these $S^{-1}A\subset A_{\mathfrak q}$, so $f,f^{-1}\in A_{\mathfrak q}$);
hence $f,f^{-1}\in\bigcap_{\operatorname{ht}\mathfrak q=1}A_{\mathfrak q}=A$
($A$ noetherian normal: *reference: Stacks Project, Algebra,
a noetherian normal domain is the intersection of its localizations at
height-one primes*), i.e. $f\in A^\times$. *Surjectivity:* as $A$ is
a UFD, each height-one prime $\mathfrak q$ is principal,
$\mathfrak q=(\pi)$ with $\pi$ a prime element; if $s\in\mathfrak q\cap S$
then $s=\pi a$ with $s$ invertible in $S^{-1}A$, so
$\pi\in(S^{-1}A)^\times$, and $\operatorname{ord}_{\mathfrak q'}\pi=\delta_{\mathfrak q\mathfrak q'}$
(if $\pi\in\mathfrak q'$ with $\operatorname{ht}\mathfrak q'=1$ then
$\mathfrak q=(\pi)\subseteq\mathfrak q'$, so $\mathfrak q=\mathfrak q'$).
So the basis vectors, hence all of $\bigoplus_{\mathfrak q}\mathbf Z$,
lie in the image. (For $X$ of dimension one, $A$ is a discrete
valuation ring, $S^{-1}A$ is its fraction field, and this is the
computation in the proof of [lem-sc-divisor-exact-sequence].)
