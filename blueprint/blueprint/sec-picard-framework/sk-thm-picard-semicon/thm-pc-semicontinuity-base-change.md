+++
id = "thm-pc-semicontinuity-base-change"
kind = "theorem"
title = "Semicontinuity and base change"
order = 676
uses = ["def-pc-base-change", "def-pc-derived-direct-image", "def-pc-derived-pullback", "def-pc-morphism-conventions", "def-pc-perfect-complex", "lem-pc-flat-complex-derived-pullback", "lem-pc-rf-perfect-base-change"]
lean = ["AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber"]
+++
Let $f:X\to T$ be a proper morphism of finite presentation and let
$\mathcal F$ be an $\mathcal O_X$-module of finite presentation, flat
over $T$. For $t\in T$ write $X_t=X\times_T\operatorname{Spec}\kappa(t)$
and let $\mathcal F_t$ be the pullback of $\mathcal F$ to $X_t$. Fix an
integer $q$.

1. For every $t\in T$ the space $H^q(X_t,\mathcal F_t)$ is finite
   dimensional over $\kappa(t)$, and there is a canonical base-change map
   $$
   \varphi^q(t):\;R^qf_*\mathcal F\otimes_{\mathcal O_T}\kappa(t)
   \longrightarrow H^q(X_t,\mathcal F_t).
   $$
2. The function
   $\beta^q(t)=\dim_{\kappa(t)}H^q(X_t,\mathcal F_t)$ is upper
   semicontinuous on $T$.
3. If $T$ is reduced and $\beta^q$ is locally constant on $T$, then
   $R^qf_*\mathcal F$ is a finite locally free $\mathcal O_T$-module (in
   particular it is flat over $T$), and $\varphi^q(t)$ is an isomorphism
   for every $t\in T$.

The reducedness hypothesis in (3) cannot be omitted: over a
non-reduced base, $T$ may even be a single point (so that $\beta^q$ is
trivially constant) while $R^qf_*\mathcal F$ is not flat.

## Proof

*Local model.* Put $E=Rf_*\mathcal F$, the
derived direct image. By
[lem-pc-rf-perfect-base-change], $E$ is perfect and for every
$g:T'\to T$ the canonical map $Lg^*E\to Rf_{T',*}\mathcal F_{T'}$ is an
isomorphism. Fix $t\in T$. By [def-pc-perfect-complex] there is an
affine open $U=\operatorname{Spec}(A)\ni t$ on which $E|_U$ is
isomorphic to the complex associated with a bounded complex of finite
projective $A$-modules. Each of these finitely many modules is free on
some principal open neighbourhood of $t$; the intersection of these
neighbourhoods is again principal, and localisation of the complex
represents the restriction. Shrinking $U$, we may therefore assume

$$
E|_U\cong\widetilde K,\qquad
K:\;0\to K^a\xrightarrow{d^a}K^{a+1}\to\cdots\to K^b\to0,\qquad
K^i\cong A^{n_i}.
$$

Since higher direct images commute with restriction to open subsets
of the base, $R^qf_*\mathcal F|_U=\widetilde{H^q(K)}$. For
$s\in U$ let $g_s:\operatorname{Spec}\kappa(s)\to T$ be the canonical
morphism. The terms of $K$ are free, hence flat, so by
[lem-pc-flat-complex-derived-pullback] the derived pullback
$Lg_s^*E$ is represented by $K\otimes_A\kappa(s)$. By the base-change
isomorphism above,
$K\otimes_A\kappa(s)\cong Rf_{s,*}\mathcal F_s$, where
$f_s:X_s\to\operatorname{Spec}\kappa(s)$. The target is a one-point
space, on which the $q$-th higher direct image is the $q$-th cohomology
group; hence

$$
H^q(X_s,\mathcal F_s)\cong H^q(K\otimes_A\kappa(s)),
$$

a finite dimensional $\kappa(s)$-vector space.

*(1).* The map $\varphi^q(t)$ is the canonical base-change map
$g_t^*R^qf_*\mathcal F\to R^qf_{t,*}\mathcal F_t$ attached to the
cartesian square with bottom arrow $g_t$. In the local model it is
the evident map

$$
H^q(K)\otimes_A\kappa(s)\longrightarrow H^q(K\otimes_A\kappa(s)),\qquad
[z]\otimes1\longmapsto[z\otimes1],
$$

which is well defined because a cycle (resp. boundary) of $K$ maps to
a cycle (resp. boundary) of $K\otimes_A\kappa(s)$.

*(2).* Write $d^i(s)=d^i\otimes_A\kappa(s)$ for the matrix of $d^i$
with entries reduced to $\kappa(s)$, and let
$\rho_i(s)=\operatorname{rank}d^i(s)$. Linear algebra over $\kappa(s)$
gives

$$
\beta^q(s)=n_q-\rho_q(s)-\rho_{q-1}(s)\qquad(s\in U).
$$

For every integer $r$, the set $\{s:\rho_i(s)\ge r\}$ is the set of
points at which some $r\times r$ minor of $d^i$ does not vanish, i.e.
the complement of the closed set $V(I_r(d^i))$ cut out by the ideal of
$r\times r$ minors. Hence each $\rho_i$ is lower semicontinuous on
$U$, so $\beta^q$ is upper semicontinuous on $U$. Such opens $U$ cover
$T$, and upper semicontinuity is local, which proves (2).

*(3).* Now let $T$ be reduced, hence $A$ reduced, and let $\beta^q$ be
locally constant. Shrinking $U$ around $t$ we may assume $\beta^q$ is
constant on $U$, so $\rho_q+\rho_{q-1}=c$ is constant. Then
$\rho_q=c-\rho_{q-1}$ is also upper semicontinuous, hence locally
constant, and likewise $\rho_{q-1}$. Shrinking $U$ once more, we may
assume $\rho_q\equiv r$ and $\rho_{q-1}\equiv r'$ on $U$.

*Claim.* Let $\phi:A^m\to A^n$ be a matrix over a reduced ring $A$
whose rank at every point of $\operatorname{Spec}(A)$ equals $r$. Then
every point has a principal open neighbourhood over which, in suitable
bases, $\phi=\begin{pmatrix}I_r&0\\0&0\end{pmatrix}$. Indeed, every
$(r+1)\times(r+1)$ minor of $\phi$ vanishes in every residue field,
hence lies in every prime ideal, hence is nilpotent, hence is $0$ since
$A$ is reduced. At a given point some $r\times r$ minor $\delta$ is
nonzero, so $\delta$ is a unit on $D(\delta)$. After permuting bases,
$\phi=\begin{pmatrix}D&B\\C&F\end{pmatrix}$ with $D$ invertible over
$A_\delta$; invertible row and column operations bring $\phi$ to
$\begin{pmatrix}I_r&0\\0&F'\end{pmatrix}$ with $F'=F-CD^{-1}B$. The
$(r+1)\times(r+1)$ minors of the new matrix are
$A_\delta$-linear combinations of those of $\phi$ (Cauchy–Binet), so
they vanish; the minor formed by $I_r$ and one entry of $F'$ equals
that entry, so $F'=0$.

Apply the claim to $d^q$ and to $d^{q-1}$ and shrink $U$ to a principal
open neighbourhood of $t$ on which both normal forms hold (the bases
used for the two maps need not agree). Then
$Z=\ker d^q$ is a direct summand of $K^q$, free of rank $n_q-r$, with a
complement $Z'$ mapped by $d^q$ isomorphically onto a direct summand of
$K^{q+1}$; and $B=\operatorname{im}d^{q-1}$ is a direct summand of
$K^q$, free of rank $r'$, with $K^{q-1}\to B$ a split surjection.
Since $B\subseteq Z$, a retraction $K^q\to B$ restricts to a retraction
$Z\to B$, so $B$ is a direct summand of $Z$ and

$$
H^q(K)=Z/B
$$

is a finite projective $A$-module of rank $n_q-r-r'=\beta^q(t)$. Being
finite projective, it is locally free on principal opens, so
$R^qf_*\mathcal F$ is finite locally free near $t$, in particular flat.

For $s\in U$ split injections and split surjections remain so after
$\otimes_A\kappa(s)$. Thus $d^q(s)$ is injective on
$Z'\otimes\kappa(s)$ and zero on $Z\otimes\kappa(s)$, giving
$\ker d^q(s)=Z\otimes_A\kappa(s)$; and
$\operatorname{im}d^{q-1}(s)=B\otimes_A\kappa(s)$ inside
$K^q\otimes_A\kappa(s)$. The split exact sequence
$0\to B\to Z\to Z/B\to0$ stays exact after tensoring, so

$$
H^q(K\otimes_A\kappa(s))
=\frac{Z\otimes_A\kappa(s)}{B\otimes_A\kappa(s)}
=H^q(K)\otimes_A\kappa(s),
$$

and the identification is exactly the map of (1). Hence $\varphi^q(s)$
is an isomorphism for all $s\in U$. Since $t$ was arbitrary, (3)
follows.

*Why reducedness is needed.* Let $A=k[\varepsilon]/(\varepsilon^2)$ and let
$E_0$ be an elliptic curve over the field $k$. Let $\mathcal L$ be an invertible
sheaf on $E_0\times_k\operatorname{Spec}A$ that restricts to
$\mathcal O_{E_0}$ but is a nontrivial first-order deformation of it
(these are classified by the nonzero elements of
$H^1(E_0,\mathcal O_{E_0})\cong k$). A global section of $\mathcal L$
reduces to a constant on $E_0$. A nonzero constant cannot lift, since
a lift would trivialise $\mathcal L$. Hence
$H^0(\mathcal L)=\varepsilon H^0(E_0,\mathcal O_{E_0})\cong k$, a
module killed by $\varepsilon$ and so not flat over $A$. The base is a
single point, so $\beta^0$ is constant.
