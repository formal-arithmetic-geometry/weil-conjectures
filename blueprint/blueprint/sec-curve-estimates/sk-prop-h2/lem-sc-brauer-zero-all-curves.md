+++
id = "lem-sc-brauer-zero-all-curves"
kind = "lemma"
title = "The Brauer group of an arbitrary curve"
order = 960
uses = ["def-br", "def-sc-curves", "def-sc-etale-qcoherent-module", "def-sc-normalization", "def-weil-pbc-etale-cohomology", "lem-sc-brauer-zero", "lem-sc-cech-spectral", "lem-sc-etale-affine-qcoherent", "lem-sc-normalization-exists", "lem-sc-normalized-curve-smooth", "lem-sc-point-z-cohomology"]
+++
Let $C$ be a curve over algebraically closed $k$ in the sense of
[def-sc-curves]; $C$ may be singular, non-reduced, disconnected or
have zero-dimensional components. Then its Brauer group ([def-br])
vanishes:

$$
H^2(C_{\Et},\mathbf G_m)=0,
$$

with cohomology as in [def-weil-pbc-etale-cohomology].

## Proof

Throughout we use two standard facts about a closed immersion
$i:Z\to X$. First, $i_*$ is exact on etale abelian sheaves:
$(i_*G)_{\bar x}$ is $G_{\bar x}$ if $\bar x$ lies over a point of
$Z$ and $0$ otherwise. Second, $i_*$ has the exact left adjoint
$i^*$, so it preserves injectives and
$H^q(X,i_*G)=H^q(Z,G)$. The same two facts hold for a finite
morphism $\nu$. Its direct image is exact because
$(\nu_*G)_{\bar x}=\bigoplus_{\bar y\mapsto\bar x}G_{\bar y}$
(*classical: Stacks Project, Etale Cohomology, section on finite
morphisms*), so $H^q(X,\nu_*G)=H^q(X',G)$.

*Step 1 (reduction to $C$ reduced).* Let $\mathcal N\subseteq\mathcal O_C$
be the nilradical. It is a coherent ideal with $\mathcal N^m=0$ for
some $m$, since $C$ is noetherian. Let $i:C_{\rm red}\to C$ be the
closed immersion. For an etale $u:V\to C$, the morphism $u$ is flat,
so $u^*\mathcal N=\mathcal N\mathcal O_V$ is the ideal of
$V\times_CC_{\rm red}$. This scheme is etale over the reduced scheme
$C_{\rm red}$, hence reduced, so it is $V_{\rm red}$. Hence, with the
etale sheaves of [def-sc-etale-qcoherent-module], there is a
sequence of etale sheaves on $C$

$$
1\longrightarrow1+\mathcal N_{\rm et}\longrightarrow\mathbf G_{m,C}
\longrightarrow i_*\mathbf G_{m,C_{\rm red}}\longrightarrow1 .
$$

It is exact on every affine etale $V$: the map
$\mathcal O(V)\to\mathcal O(V_{\rm red})$ is surjective, and an element
lifting a unit modulo a nilpotent ideal is a unit. Hence it is
exact as a sequence of sheaves. For $j\ge1$ the map
$1+a\mapsto a$ induces an isomorphism of abelian sheaves

$$
(1+\mathcal N^j_{\rm et})/(1+\mathcal N^{j+1}_{\rm et})
\xrightarrow{\ \sim\ }(\mathcal N^j/\mathcal N^{j+1})_{\rm et}.
$$

It is a homomorphism because $(1+a)(1+b)=1+a+b+ab$ with
$ab\in\mathcal N^{2j}\subseteq\mathcal N^{j+1}$. It is surjective, and
its kernel is $1+\mathcal N^{j+1}_{\rm et}$. Both claims can be checked
on affine etale $V$, where $u$ is flat and so
$0\to u^*\mathcal N^{j+1}\to u^*\mathcal N^j\to
u^*(\mathcal N^j/\mathcal N^{j+1})\to0$ is exact.

*Claim.* For every quasi-coherent $\mathcal O_C$-module $\mathcal F$,
$H^q(C_{\Et},\mathcal F_{\rm et})=0$ for $q\ge2$. Indeed, let
$\mathfrak U=\{U_1,\dots,U_r\}$ be a finite affine open covering of
the quasi-compact scheme $C$. Since $C$ is separated, all finite
intersections $U_{i_0}\cap\dots\cap U_{i_p}$ are affine. By
[lem-sc-etale-affine-qcoherent], $\mathcal F_{\rm et}$ has no higher
cohomology on them. So the spectral sequence of [lem-sc-cech-spectral]
degenerates and gives
$H^q(C_{\Et},\mathcal F_{\rm et})=\check H^q(\mathfrak U,\mathcal F)$.
The same argument on the Zariski site, which [lem-sc-cech-spectral]
also covers, with Serre's vanishing of quasi-coherent cohomology on
affine schemes, identifies this Cech group with the Zariski group
$H^q(C,\mathcal F)$. This group vanishes for $q>\dim C$, and so for
$q\ge2$, by Grothendieck's vanishing theorem on a noetherian
topological space (*Stacks Project, Cohomology of Sheaves, section on
vanishing on noetherian topological spaces*).

By the claim, $H^2(C,(\mathcal N^j/\mathcal N^{j+1})_{\rm et})=0$ for
every $j$. Descending induction on $j$ gives
$H^2(C,1+\mathcal N^j_{\rm et})=0$ for all $j\ge1$: the case
$j\ge m$ is the trivial sheaf, and the inductive step uses the
long exact sequence of
$1\to1+\mathcal N^{j+1}_{\rm et}\to1+\mathcal N^j_{\rm et}
\to(\mathcal N^j/\mathcal N^{j+1})_{\rm et}\to0$. The long exact
sequence of the first display, together with
$H^2(C,i_*\mathbf G_m)=H^2(C_{\rm red},\mathbf G_m)$, now gives an
injection

$$
H^2(C,\mathbf G_m)\hookrightarrow H^2(C_{\rm red},\mathbf G_m).
$$

Since $C_{\rm red}$ is again a curve, we may assume $C$ reduced.

*Step 2 (normalization).* Let $C$ be reduced with irreducible
components $X_1,\dots,X_r$, taken with their reduced structure. These
are integral schemes of finite type over $k$ of dimension at most
one. Let $\nu_i:X_i^{\nu}\to X_i$ be the normalization
([def-sc-normalization]), put $C':=\coprod_iX_i^{\nu}$, and let
$\nu:C'\to C$ be the induced morphism. By [lem-sc-normalization-exists]
each $\nu_i$ is finite, surjective and birational, so $\nu$ is finite
and surjective. Each $X_i^{\nu}$ is described as follows.
- If $\dim X_i=0$, then $X_i$ is the spectrum of a finite field
  extension of $k$, so $X_i=X_i^{\nu}=\operatorname{Spec}k$.
- If $\dim X_i=1$, then $X_i^{\nu}$ is a smooth ([lem-sc-normalized-curve-smooth],
  $k$ being perfect), integral, one-dimensional scheme. It is
  separated and of finite type, being finite over $C$. So it is a
  smooth separated connected curve.

Consider the map $\mathbf G_{m,C}\to\nu_*\mathbf G_{m,C'}$. It is
injective. Let $V\to C$ be etale and $f\in\mathcal O(V)^\times$ with
$f=1$ on $V\times_CC'$. Then $f-1$ vanishes in the residue field of
every point of $V\times_CC'$. This scheme surjects onto $V$, and residue
fields only grow, so $f-1$ vanishes at every point of $V$. Since $V$ is
etale over the reduced $C$, it is reduced, so $f=1$. Let $\mathcal Q$ be
the cokernel, so that

$$
1\longrightarrow\mathbf G_{m,C}\longrightarrow\nu_*\mathbf G_{m,C'}
\longrightarrow\mathcal Q\longrightarrow1
$$

is exact. Let $Z\subseteq C$ be the support of the coherent
$\mathcal O_C$-module $\nu_*\mathcal O_{C'}/\mathcal O_C$. It is
closed. It contains no generic point $\xi_i$ of a component. Indeed
$\mathcal O_{C,\xi_i}$ is a reduced zero-dimensional local ring,
hence the field $k(X_i)$. Over $\operatorname{Spec}k(X_i)$ the map
$\nu$ is the birational map
$\operatorname{Spec}k(X_i)\to\operatorname{Spec}k(X_i)$, since the
$X_j^{\nu}$ with $j\neq i$ lie over $X_j\not\ni\xi_i$. So $Z$ is a proper
closed subset of each component. It is therefore a finite set of
closed points, a proper closed subset of an irreducible scheme of
dimension at most one being finite. Over $U:=C\setminus Z$ we have
$\nu_*\mathcal O_{C'}|_U=\mathcal O_U$. Since $\nu$ is affine,
$\nu^{-1}(U)\to U$ is an isomorphism. Hence $\mathcal Q|_U=0$, because
$\nu_*$ commutes with restriction to the etale $U$. Give $Z$ its
reduced structure, so that $Z\cong\coprod_{z\in Z}\operatorname{Spec}k$,
and let $i_Z:Z\to C$. Then $\mathcal Q\to i_{Z*}i_Z^*\mathcal Q$ is
an isomorphism, as one checks on geometric stalks. For $q\ge1$ this
gives

$$
H^q(C,\mathcal Q)=H^q(Z,i_Z^*\mathcal Q)
=\prod_{z\in Z}H^q(\operatorname{Spec}k,(i_Z^*\mathcal Q)_z)=0.
$$

The last equality holds because, as in the proof of
[lem-sc-point-z-cohomology], the etale topos of $\operatorname{Spec}k$
for algebraically closed $k$ is the category of abelian groups and
global sections is the exact stalk functor. This holds for every
coefficient sheaf, not only $\mathbf Z$. The long exact sequence of
the last display, together with
$H^2(C,\nu_*\mathbf G_{m,C'})=H^2(C',\mathbf G_m)$, gives

$$
0=H^1(C,\mathcal Q)\longrightarrow H^2(C,\mathbf G_m)
\longrightarrow H^2(C',\mathbf G_m)
=\prod_iH^2(X_i^{\nu},\mathbf G_m).
$$

A factor with $X_i^{\nu}=\operatorname{Spec}k$ is zero by the same
remark about $\operatorname{Spec}k$. A factor with $X_i^{\nu}$ a smooth
separated connected curve is zero by [lem-sc-brauer-zero]. Hence
$H^2(C,\mathbf G_m)=0$. (This is the classical vanishing of the
Brauer group of a curve over an algebraically closed field:
*reference: Grothendieck, Le groupe de Brauer III; Milne, Etale
Cohomology, Ch. III*.)
