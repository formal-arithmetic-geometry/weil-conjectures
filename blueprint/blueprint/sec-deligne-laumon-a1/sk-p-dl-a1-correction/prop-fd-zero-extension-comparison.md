+++
id = "prop-fd-zero-extension-comparison"
kind = "theorem"
tags = ["latex:proposition"]
title = "The zero-extension comparison"
order = 2768
uses = ["def-a1-constituent-nonexceptional", "def-fd-artin-schreier-sheaf", "def-fd-kernel", "def-fd-transform", "def-weil-punctual-weights", "def-wf-middle-extension", "lem-fd-as-trace", "lem-fd-first-formula", "lem-wf-boundary-semicontinuity", "prop-a1-fourier-middle-extension", "rem-dl-a1-conventions", "thm-fd-transform-well-defined"]
lean = ["AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection", "AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.nonempty_fourierCorrection", "AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection.isLisse", "AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection.hasWeightsAtMost"]
+++
In the conventions of [rem-dl-a1-conventions], let
$j:U_0\hookrightarrow A_0$ be a dense open immersion with finite
complement $S_0$, and let $\mathcal M$ be a nonzero irreducible lisse
Weil sheaf on $U_0$ which is constituent-nonexceptional in the sense of
[def-a1-constituent-nonexceptional] and punctually $\iota$-pure of
weight $w$. Let $j':U'_0\hookrightarrow A'_0$ and $\mathcal M'$ be as in
[prop-a1-fourier-middle-extension], so that
$\operatorname{FT}_\psi\bigl((j_*\mathcal M)[1]\bigr)\cong
(j'_*\mathcal M')[1]$ for the transform of [def-fd-transform], and put

$$
\mathcal B:=j_*\mathcal M/j_!\mathcal M ,
$$

with $j_*$ the middle extension of [def-wf-middle-extension]. Then there
are Weil sheaves $\mathcal G$ and $\mathcal B'$ on the dual line $A'_0$
such that

$$
\operatorname{FT}_\psi\bigl(j_!\mathcal M[1]\bigr)\cong\mathcal G[1],
\qquad
\operatorname{FT}_\psi(\mathcal B)\cong\mathcal B'[1],
\qquad
0\longrightarrow\mathcal B'\longrightarrow\mathcal G\longrightarrow
j'_*\mathcal M'\longrightarrow0 .
$$

The correction $\mathcal B'$ is lisse on the entire dual line $A'_0$, and
it has weights at most $w$: for every closed point $y$ of $A'_0$ and
every eigenvalue $\alpha$ of the local Frobenius $F_y$ on
$\mathcal B'_{\bar y}$,

$$
|\iota(\alpha)|^2\le q_y^{\,w}.
$$

In particular the transform of $j_!\mathcal M[1]$ is a sheaf shifted by
one without assuming geometric irreducibility of $\mathcal M$ or
unramifiedness at infinity.

## Proof

*Step 1: the boundary sheaf.* The map $j_!\mathcal M\to j_*\mathcal M$ is
an isomorphism over $U_0$ and $j_!\mathcal M$ has zero stalks on $S_0$,
so it is injective and $\mathcal B$ vanishes on $U_0$. Hence
$\mathcal B$ is supported on the finite reduced closed subscheme $S_0$,
and

$$
\mathcal B\cong\bigoplus_{s\in S_0}i_{s*}E_s,
\qquad E_s:=(j_*\mathcal M)_{\bar s},
$$

where $i_s:s\hookrightarrow A_0$ is the inclusion of the closed point
$s$ and $E_s$ is the boundary stalk with its Frobenius $F_s$, a
finite-dimensional Weil module of the residue field $k(s)$ of degree
$d(s)$ over $k_0$.

*Step 2: the transform of a boundary point.* Fix $s\in S_0$ and a Weil
module $E$ of $k(s)$. Put $A'_s:=s\times_{k_0}A'_0=A'_0\otimes_{k_0}k(s)$,
let $i'_s:A'_s\hookrightarrow A_0\times A'_0$ be the base change of $i_s$
along the first projection $p_1$, let $\pi_s=p_2\circ i'_s:A'_s\to A'_0$
be the base change of $\operatorname{Spec}k(s)\to\operatorname{Spec}k_0$,
which is finite étale of degree $d(s)$, and let
$q_s:A'_s\to s$ be the projection. Pullback commutes with direct image
along the closed immersion $i_s$, so $p_1^*i_{s*}E\cong i'_{s*}q_s^*E$,
and the projection formula for the closed immersion $i'_s$ gives
$i'_{s*}q_s^*E\otimes\mathcal K_\psi\cong
i'_{s*}\bigl(q_s^*E\otimes i'^*_s\mathcal K_\psi\bigr)$ for the kernel
$\mathcal K_\psi$ of [def-fd-kernel]. The pairing restricted to
$A'_s$ is the linear function $f_s:\xi\mapsto s\xi$, so
$\mathcal L_s:=i'^*_s\mathcal K_\psi=f_s^*\mathcal L_\psi$ is the
Artin–Schreier sheaf of [def-fd-artin-schreier-sheaf] attached to
$s\xi$, a lisse sheaf of rank one. Since
$p_{2!}\,i'_{s*}=(p_2 i'_s)_!=\pi_{s!}=\pi_{s*}$, the last because
$\pi_s$ is finite, the definition [def-fd-transform] gives

$$
\operatorname{FT}_\psi(i_{s*}E)\cong
\pi_{s*}\bigl(q_s^*E\otimes\mathcal L_s\bigr)[1].
$$

This is the computation of the second formula of [lem-fd-first-formula]
(the case $s=0$, $E=\overline{\mathbf Q}_\ell$) at a general closed
point. As the transform is additive, Step 1 gives
$\operatorname{FT}_\psi(\mathcal B)\cong\mathcal B'[1]$ with

$$
\mathcal B':=\bigoplus_{s\in S_0}
\pi_{s*}\bigl(q_s^*E_s\otimes\mathcal L_s\bigr).
$$

*Step 3: $\mathcal B'$ is lisse.* Each $q_s^*E_s\otimes\mathcal L_s$ is
lisse on $A'_s$. After the base change to $k$, the finite étale map
$\pi_s$ becomes the projection
$A'\times\operatorname{Hom}_{k_0}(k(s),k)\to A'$ from a disjoint union
of $d(s)$ copies of $A'$, so the direct image becomes a direct sum of
$d(s)$ lisse sheaves on $A'$. Hence each summand, and $\mathcal B'$,
is lisse on the whole dual line.

*Step 4: the weights of $\mathcal B'$.* Since $\mathcal M$ is
punctually pure of weight $w$, it is punctually of weights at most $w$ in
the sense of [def-weil-punctual-weights], and the boundary
semicontinuity [lem-wf-boundary-semicontinuity] on the curve $A_0$ with
$\beta=w$ gives $|\iota(\mu)|^2\le q_s^{\,w}$ for every eigenvalue $\mu$
of $F_s$ on $E_s$.

Fix $s\in S_0$, put $\mathcal F_s:=q_s^*E_s\otimes\mathcal L_s$, and let
$z$ be a closed point of $A'_s$ of degree $n$ over $k_0$. Its image in
$s$ gives $d(s)\mid n$, and the local Frobenius $F_z$ acts on the stalk
of $q_s^*E_s$ as $F_s^{\,n/d(s)}$, whose eigenvalues are the
$(n/d(s))$-th powers of those of $F_s$ and so have squared modulus at
most $q_s^{\,wn/d(s)}=q^{wn}$. On the rank-one stalk of
$\mathcal L_s=f_s^*\mathcal L_\psi$ the operator $F_z$ acts as
$F_u^{\,n/d(u)}$, where $u=f_s(z)$ is the image closed point of the line;
by [lem-fd-as-trace] $F_u$ acts by the $p$-th root of unity
$\psi(\operatorname{Tr}_{\kappa(u)/k_0}(u))$. Hence every
eigenvalue of $F_z$ on $(\mathcal F_s)_{\bar z}$ has squared
$\iota$-modulus at most $q^{wn}$.

Now let $y$ be a closed point of $A'_0$ with geometric point $\bar y$.
The stalk of the finite direct image is the sum over the geometric
points of $A'_s$ above $\bar y$,

$$
(\pi_{s*}\mathcal F_s)_{\bar y}=\bigoplus_{\bar z\mapsto\bar y}
(\mathcal F_s)_{\bar z},
$$

and $F_y$ permutes these summands. Its orbits correspond to the closed
points $z$ of $A'_s$ above $y$; if the orbit of $\bar z$ has length $e$,
then $z$ has degree $n=e\,d(y)$ and $F_y^{\,e}$ maps the summand at
$\bar z$ to itself, acting there as $F_z$. Let $\alpha$ be an eigenvalue
of $F_y$ with eigenvector $v=(v_{\bar z})$, and choose $\bar z$ with
$v_{\bar z}\ne0$, of orbit length $e$. Since $F_y^{\,e}$ preserves each
summand of that orbit, comparing components of $F_y^{\,e}v=\alpha^ev$
gives $F_zv_{\bar z}=\alpha^ev_{\bar z}$. By the previous paragraph
$|\iota(\alpha)|^{2e}\le q^{we\,d(y)}$, that is
$|\iota(\alpha)|^2\le q_y^{\,w}$. An eigenvalue of $F_y$ on the finite
direct sum $\mathcal B'_{\bar y}$ is an eigenvalue on one of its
summands, which proves the weight bound.

*Step 5: concentration and the exact sequence.* The short exact sequence
$0\to j_!\mathcal M\to j_*\mathcal M\to\mathcal B\to0$ of Step 1 gives a
distinguished triangle
$j_!\mathcal M[1]\to(j_*\mathcal M)[1]\to\mathcal B[1]\to$. The transform
is an exact triangulated functor by [thm-fd-transform-well-defined];
by [prop-a1-fourier-middle-extension] and Step 2, and after rotation,
this gives a distinguished triangle

$$
\mathcal B'[1]\longrightarrow K\longrightarrow(j'_*\mathcal M')[1]
\longrightarrow\mathcal B'[2],
\qquad K:=\operatorname{FT}_\psi\bigl(j_!\mathcal M[1]\bigr).
$$

Both outer terms have a single cohomology sheaf, in degree $-1$. The
long exact sequence of cohomology sheaves therefore gives
$\mathcal H^aK=0$ for $a\ne-1$, so $K\cong\mathcal G[1]$ with
$\mathcal G:=\mathcal H^{-1}K$, and in degree $-1$ it reads

$$
0=\mathcal H^{-2}\bigl((j'_*\mathcal M')[1]\bigr)\to\mathcal B'\to
\mathcal G\to j'_*\mathcal M'\to\mathcal H^{0}\bigl(\mathcal B'[1]\bigr)=0,
$$

which is the asserted exact sequence. All objects and maps carry the Weil
structure, since the transform and the triangles are formed in the Weil
category.
