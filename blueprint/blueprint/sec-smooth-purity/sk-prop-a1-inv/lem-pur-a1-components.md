+++
id = "lem-pur-a1-components"
kind = "lemma"
title = "The connected components of the affine line over a base"
order = 1958
uses = ["def-pur-conventions", "def-sbc-affine-space", "def-weil-scheme-morphism-properties", "sbc-lem-affine-space-smooth"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $B$ be a nonempty
separated finite-type
$k$-scheme, let $\mathbf A^1_B=\operatorname{Spec}(\mathcal O_B[t])$ be the affine line of [def-sbc-affine-space], let
$s_0:B\hookrightarrow\mathbf A^1_B$ be the zero section, the closed
immersion defined by $t=0$, and let
$\mathbf G_{m,B}=\mathbf A^1_B\setminus s_0(B)$ be the complement of
the zero section. Let $1:B\to\mathbf A^1_B$ be the unit section,
the section defined by $t=1$ of the projection, which factors through
$\mathbf G_{m,B}$.

1. The connected components of $\mathbf A^1_B$, and those of
$\mathbf G_{m,B}$, are exactly the inverse images of the
connected components of $B$.
1. Every connected component of $\mathbf A^1_B$ meets
$\mathbf G_{m,B}$, and meets the image of the unit section
$1$.
1. Every connected component of $\mathbf G_{m,B}$ meets the image
of the unit section $1$.

## Proof

Step 1: openness and connected fibres. The projection
$\pi:\mathbf A^1_B\to B$ of [def-sbc-affine-space] is smooth of
relative dimension $1$ by [sbc-lem-affine-space-smooth], hence
flat and locally of finite presentation; the same holds for
$\pi':\mathbf G_{m,B}\to B$, which is the composite of the open
immersion $\mathbf G_{m,B}\hookrightarrow\mathbf A^1_B$ with
$\pi$, an open immersion being flat and locally of finite
presentation and both properties being stable under composition. A
flat morphism locally of finite presentation is universally open
(Stacks Project, Lemma 29.26.10,
[Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)). The
fibres of $\pi$ and of $\pi'$ over a point $y\in B$ are
$\mathbf A^1_{\kappa(y)}=\operatorname{Spec}(\kappa(y)[t])$ and
$\mathbf G_{m,\kappa(y)}=\operatorname{Spec}(\kappa(y)[t,t^{-1}])$:
both rings are domains, so both fibres are nonempty and connected.
Step 2: the components. Since $k$ is a field and $B$ is a
[def-weil-scheme-morphism-properties] finite-type $k$-scheme, it
is Noetherian; a Noetherian space has finitely many irreducible
components, hence finitely many connected components, and each of them
is the complement of the union of the others, hence open as well as
closed. Let $D\subseteq B$ be a connected component. Then
$\pi^{-1}(D)$ is open and closed in $\mathbf A^1_B$, and it is
connected: if $\pi^{-1}(D)=U\sqcup V$ with $U,V$ open and
nonempty, then every fibre of $\pi$ over a point of $D$, being
nonempty and connected, lies entirely in $U$ or entirely in $V$;
consequently $D=\pi(U)\sqcup\pi(V)$ is a disjoint union of nonempty
open subsets, $\pi(U)$ and $\pi(V)$ being open because $\pi$ is
open, which contradicts the connectedness of $D$. As $D$ runs
over the finitely many connected components of $B$, the sets
$\pi^{-1}(D)$ are pairwise disjoint open connected subsets covering
$\mathbf A^1_B$, so they are its connected components. The same
argument with $\pi'$ in place of $\pi$ identifies the connected
components of $\mathbf G_{m,B}$. This is (1).
Step 3: the sections. Let $\pi^{-1}(D)$ be a connected component of
$\mathbf A^1_B$. Choose a point $y\in D$, which is nonempty; the
fibre $\pi^{-1}(y)=\mathbf A^1_{\kappa(y)}$ contains the unit point
$t=1$, which lies in $\mathbf G_{m,B}$ and is the image of
$1(y)$ under the unit section. Hence $\pi^{-1}(D)$ meets
$\mathbf G_{m,B}$ and meets the image of the unit section, which is
(2); the same argument for the components $\pi'^{-1}(D)$ of
$\mathbf G_{m,B}$ gives (3).
