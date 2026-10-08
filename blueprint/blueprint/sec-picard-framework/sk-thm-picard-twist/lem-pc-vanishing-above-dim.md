+++
id = "lem-pc-vanishing-above-dim"
kind = "lemma"
title = "Vanishing above the dimension of a curve"
order = 759
uses = ["def-pc-curve", "def-pc-degree-line-bundle", "def-pc-dimension", "def-pc-divisor-line-bundle", "def-pc-projective-morphism", "def-pc-smooth-projective-curve", "def-sc-ample", "def-sc-effective-cartier-divisor", "lem-pc-ample-positive-degree", "lem-pc-cech-computes", "lem-pc-euler-additive", "lem-pc-projective-proper", "lem-sc-ample-complement-affine", "lem-sc-point-cartier", "lem-sc-regular-dim1-dvr", "lem-sc-smooth-regular"]
+++
Let $k$ be a field and let $X$ be a
curve over $k$ which is smooth and
projective. For every
quasi-coherent $\mathcal{O}_X$-module $\mathcal{F}$ one has

$$
H^i(X,\mathcal{F})=0\qquad\text{for all }i\ge2 .
$$

(EGA III$_1$, (3.2.1): cohomology of a Noetherian scheme of
dimension $d$ vanishes above $d$; here $d=1$.)

## Proof

*Step 1: the point $P$ and the first affine open.* The curve $X$
is proper (a projective morphism is proper,
[lem-pc-projective-proper]), nonempty (an integral scheme,
[def-pc-curve]) and of finite
type over $k$, hence has a closed point: any nonempty open affine
$\operatorname{Spec}(A)\subseteq X$ has $A$ a nonzero
finite type $k$-algebra, so
$A$ has a maximal ideal (the classical Nullstellensatz: a maximal
ideal exists in a nonzero finitely generated algebra over a field),
and the closed points of $\operatorname{Spec}(A)$ are exactly its maximal ideals.
Pick a closed point $P\in X$.

The local ring $\mathcal{O}_{X,P}$ is a regular local ring of dimension one
([lem-sc-smooth-regular]: smooth over a field; the curve is
one-dimensional because $\dim\mathcal{O}_{X,P}=\dim X=1$ for the closed point
$P$, [def-pc-dimension]), hence a discrete valuation ring
([lem-sc-regular-dim1-dvr]). By the argument of
[lem-sc-point-cartier] (the same proof works over an arbitrary
base field: it only uses the two lemmas just cited) the closed point
$P$ with its reduced structure is an effective Cartier divisor
([def-sc-effective-cartier-divisor]); write
$D:=[P]$ and $\mathcal{L}:=\mathcal{O}_X(D)$
([def-pc-divisor-line-bundle]), so that the support of $D$ is
$\{P\}$.

The exact sequence

$$
0\to\mathcal{O}_X\to\mathcal{O}_X(D)\to\mathcal{O}_X(D)\otimes\mathcal{O}_P\to0
$$

(the first map is multiplication by the canonical section $1_D$;
$\mathcal{O}_X(D)\otimes\mathcal{O}_P\cong k(P)$, the structure sheaf of the closed
point) is exact, $\mathcal{O}_X(D)\otimes\mathcal{O}_P$ is the skyscraper $k(P)$,
which is flasque, hence has no higher cohomology
($H^i(X,k(P))=0$ for $i\ge1$), and its $H^0$ is
$k(P)$, a $[k(P):k]$-dimensional $k$-vector space. By the additivity
of the Euler characteristic ([lem-pc-euler-additive]) and
[def-pc-degree-line-bundle],

$$
\deg\mathcal{L}=\deg[\mathcal{O}_X(D)]=\chi(\mathcal{O}_X(D))-\chi(\mathcal{O}_X)
=[k(P):k]\ge1 .
$$

Hence $\mathcal{L}$ is ample ([lem-pc-ample-positive-degree]: positive
degree is equivalent to ampleness), and by
[lem-sc-ample-complement-affine] (the complement of an ample
Cartier divisor is affine, [def-sc-ample] for the ampleness
hypothesis) the open subscheme

$$
U_1:=X\setminus\{P\}=X\setminus D
$$

is affine.

*Step 2: the second affine open.* By the standard fact that
every point of a scheme has an affine open neighbourhood, choose an
affine open $V\subseteq X$ with $P\in V$; write $V=\operatorname{Spec}(A)$ with
$A:=\mathcal{O}_X(V)$. The ring $A$ is a finitely generated $k$-algebra and
an integral domain (an affine chart of the integral scheme $X$,
[def-pc-curve]), of Krull dimension one (a nonempty open
subscheme of the one-dimensional $X$; [def-pc-dimension]), and
$P$ corresponds to a maximal ideal $\mathfrak m\subset A$ (the closed
points of $\operatorname{Spec} A$ are the maximal ideals).

*Claim: $V\setminus\{P\}$ is affine.* We show
$\operatorname{Spec}(A)\setminus\{\mathfrak m\}$ is a principal open: since
$\dim A=1$, the ideal $\mathfrak m$ is nonzero, so choose
$0\neq f\in\mathfrak m$. By Krull's principal ideal theorem every
minimal prime over $(f)$ has height $\le1$; it is nonzero because
$(f)\neq0$ and $A$ is a domain; hence it has height exactly $1$, so it
is maximal ($\dim A=1$). Let
$\mathfrak m_1,\dots,\mathfrak m_r$ be the finitely many (Noetherian
ring) minimal primes over $(f)$; they are maximal ideals and
$\mathfrak m\in\{\mathfrak m_1,\dots,\mathfrak m_r\}$ because
$f\in\mathfrak m$. If $r=1$ put $g:=f$; otherwise
$\mathfrak m\nsubseteq\mathfrak m_1\cup\cdots\cup\mathfrak m_r$
(a maximal ideal $\neq\mathfrak m_j$ is not contained in
$\mathfrak m_j$, and an ideal contained in a finite union of prime
ideals is contained in one of them: prime avoidance; this applies
since all $\mathfrak m_j$ are prime), so there is
$g\in\mathfrak m\setminus(\mathfrak m_1\cup\cdots\cup\mathfrak m_r)$.
In both cases $V(g)=\{\mathfrak m\}$: a prime
$\mathfrak p\supseteq(g)$ contains a minimal prime over $(g)$
(Noetherianity), which has height one, hence is one of the maximal
ideals $\mathfrak m_1,\dots,\mathfrak m_r$; among them only
$\mathfrak m$ contains $g$ (for $r\ge2$ by the choice of $g$; for
$r=1$ because $\mathfrak m_1=\mathfrak m$ since $f\in\mathfrak m$ with
$V(f)=\{\mathfrak m_1\}$), so $\mathfrak p=\mathfrak m$ as
$\mathfrak m$ is maximal. Therefore

$$
V\setminus\{P\}=\operatorname{Spec}(A)\setminus\{\mathfrak m\}=D(g)=\operatorname{Spec}(A_g)
$$

is affine, as claimed.

*Step 3: the two-member cover computes.* The open subschemes
$U_1$ (Step 1) and $U_2:=V$ (Step 2) cover $X$: every point of $X$
different from $P$ lies in $U_1$, and $P\in V$. The finite
intersections of the members are affine: $U_1$ by Step 1, $U_2$ by
construction, and $U_1\cap U_2=V\setminus\{P\}$ by the claim of Step
2. By [lem-pc-cech-computes] (the Cech complex of an open
affine covering computes sheaf cohomology of quasi-coherent modules
whenever all finite intersections are affine),

$$
H^i(X,\mathcal{F})=\check H^i(\{U_1,U_2\},\mathcal{F})\qquad\text{for all }i\ge0 .
$$

In the alternating Cech complex of a two-member cover the $i$-th term
is the product over the $(i+1)$-element subsets of $\{1,2\}$; there
are none as soon as $i\ge2$:

$$
\check C^i(\{U_1,U_2\},\mathcal{F})=0\qquad\text{for }i\ge2 ,
$$

so $\check H^i(\{U_1,U_2\},\mathcal{F})=0$ for all $i\ge2$, and hence
$H^i(X,\mathcal{F})=0$ for all $i\ge2$.
