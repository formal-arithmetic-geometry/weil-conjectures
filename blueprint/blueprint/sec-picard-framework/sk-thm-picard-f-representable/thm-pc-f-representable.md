+++
id = "thm-pc-f-representable"
kind = "theorem"
title = "$F$ is representable by an open subscheme of $\\underline{\\operatorname{Hilb}}^g_{X/k}$"
order = 831
uses = ["def-pc-derived-category", "def-pc-f-subfunctor", "def-pc-finite-locally-free", "def-pc-genus", "def-pc-hilb-functor", "def-pc-pic-sigma-functor", "def-pc-rational-point", "def-pc-relative-effective-cartier", "def-pc-representable-functor", "def-pc-separably-closed", "def-pc-smooth-projective-curve", "def-pc-subfunctor", "def-sc-effective-cartier-divisor", "def-sc-invertible-module", "lem-pc-cartier-criterion", "lem-pc-f-open-subfunctor", "lem-pc-flat-rf-open", "lem-pc-hilb-representable", "lem-pc-projection-formula", "lem-pc-recd-pullback", "lem-pc-rf-base-change-flat-module", "lem-pc-universal-adjoint-section", "lem-pc-universal-divisor", "lem-pc-zero-scheme-recd", "prop-pc-xk-integral", "thm-pc-hilb-curves"]
lean = ["AlgebraicGeometry.isRepresentable_picardFunctorInvertibleDirectImage"]
+++
(Picard Schemes of Curves, Lemma 44.6.4, Tag
[0B9X](https://stacks.math.columbia.edu/tag/0B9X).)
Let $k$ be a separably closed field,
let $X$ be a
smooth projective curve of
genus $g$ over $k$ with a
$k$-rational point $\sigma$, and let
$F$ be the subfunctor of
[lem-pc-f-open-subfunctor]. Then $F$ is representable by an open
subscheme of $\underline{\operatorname{Hilb}}^g_{X/k}$.

## Proof

Write $H:=\underline{\operatorname{Hilb}}^g_{X/k}$; it exists by [prop-pc-xk-integral]
(2) and [thm-pc-hilb-curves]. Let $D_{\mathrm{univ}}\subset H\times X$
be the universal divisor, and let

$$
\mathcal{L}_H:=\mathcal{O}(D_{\mathrm{univ}})\otimes
\mathrm{pr}_H^*\sigma_H^*\mathcal{O}(D_{\mathrm{univ}})^{\otimes-1}
$$

be the normalized universal module ($\sigma_H:H\to H\times X$ is the
section of $\mathrm{pr}_H$ induced by $\sigma$; the cancellation of the
$\sigma$-factors in
$\sigma_H^*\mathcal{L}_H=\sigma_H^*\mathcal{O}(D_{\mathrm{univ}})\otimes \sigma_H^*\mathrm{pr}_H^*\sigma_H^*\mathcal{O}(D_{\mathrm{univ}})^{-1}\cong\mathcal{O}_H$,
because $\mathrm{pr}_H\circ\sigma_H=\mathrm{id}_H$, shows
$\mathcal{L}_H\in\operatorname{Pic}_{X/k,\sigma}(H)$, [def-pc-pic-sigma-functor]). By the
Yoneda lemma ([def-pc-representable-functor]) the element
$\mathcal{L}_H$ defines a natural transformation $h_H\to\operatorname{Pic}_{X/k,\sigma}$.

Since $F\subseteq\operatorname{Pic}_{X/k,\sigma}$ is an open subfunctor
([lem-pc-f-open-subfunctor]), there is a maximal open $W\subseteq H$
such that $\mathcal{L}_H|_{W\times X}\in F(W)$; by
[def-pc-subfunctor] it is the open subscheme produced by
[lem-pc-flat-rf-open] (with $i=0$, $r=1$) applied to the proper
morphism of finite presentation
$p:H\times X\to H$ and the flat
invertible module
$\mathcal{O}(D_{\mathrm{univ}})$ (the twist by $\mathrm{pr}_H^*\sigma_H^*\mathcal{O}(D_{\mathrm{univ}})^{-1}$
does not affect the perfect-locus condition: by
[lem-pc-projection-formula] and [lem-pc-rf-base-change-flat-module],
$Rp_*$ commutes with tensoring by the pullback of an invertible module
from the base). Applying the Yoneda lemma again we obtain the commutative
diagram

$$
\begin{array}{ccc}
h_W & \xrightarrow{\ \psi\ } & F\\[-2pt]
\downarrow & & \downarrow\\[-2pt]
h_H & \xrightarrow{\ \ } & \operatorname{Pic}_{X/k,\sigma}
\end{array}
$$

and we show that the top horizontal arrow $\psi$ is an isomorphism.

*Construction of the inverse.* Let $\mathcal{L}\in F(T)$ for a scheme
$T$ over $k$; let $\mathcal{N}$ be an invertible $\mathcal{O}_T$-module with
$Rf_{T,*}\mathcal{L}\cong\mathcal{N}[0]$, and let $s$ be the adjoint section of
$\mathcal{L}\otimes f_T^*\mathcal{N}^{-1}$ ([lem-pc-zero-scheme-recd]). By
[lem-pc-zero-scheme-recd], $D:=Z(s)$ is a relative effective Cartier
divisor on $X_T/T$ which is finite locally free of degree $g$; hence
$D\in\operatorname{Hilb}^g_{X/k}(T)$ ([def-pc-hilb-functor]) and, by the
representability of $\operatorname{Hilb}^g_{X/k}$ ([thm-pc-hilb-curves] (1)), there
is a morphism $m:T\to H$ with $D=(m\times\mathrm{id}_X)^*D_{\mathrm{univ}}$
(the universal object of [lem-pc-universal-divisor]).

*$m$ factors through $W$.* By
[lem-pc-recd-pullback] the pullback of the relative effective
Cartier divisor $D_{\mathrm{univ}}$ along $m$ is the divisor with
associated module

$$
(m\times\mathrm{id})^*\mathcal{O}(D_{\mathrm{univ}})\cong\mathcal{O}_{X_T}(D)\cong\mathcal{M}
=\mathcal{L}\otimes f_T^*\mathcal{N}^{-1}
$$

(the second isomorphism holds because the section $s$ of $\mathcal{M}$ has zero
scheme $D$, so $s$ generates the ideal sheaf $\mathcal{I}_D$ at the points where
it does not vanish and the identification $D=Z(s)$ gives
$\mathcal{O}_{X_T}(D)=\mathcal{I}_D^\vee$; write $u$ for this isomorphism). We compute:

$$
(m\times\mathrm{id})^*\mathcal{L}_H
=(m\times\mathrm{id})^*\mathcal{O}(D_{\mathrm{univ}})
\otimes\mathrm{pr}_T^*\bigl(m^*\sigma_H^*\mathcal{O}(D_{\mathrm{univ}})\bigr)^{-1}
=\mathcal{O}_{X_T}(D)\otimes\mathrm{pr}_T^*\sigma_T^*\mathcal{O}_{X_T}(D)^{-1}
$$

(using $(m\times\mathrm{id})\circ\sigma_T=\sigma_H\circ m$ and
$(m\times\mathrm{id})^*\mathrm{pr}_H^*=\mathrm{pr}_T^*m^*$). Since $\sigma_T^*\mathcal{O}_{X_T}(D)\cong\sigma_T^*\mathcal{M}$
$=\sigma_T^*\mathcal{L}\otimes\sigma_T^*f_T^*\mathcal{N}^{-1} =\mathcal{O}_T\otimes\mathcal{N}^{-1} =\mathcal{N}^{-1}$ (because $\mathcal{L}\in\operatorname{Pic}_{X/k,\sigma}(T)$ and
$\sigma_T^*f_T^*=\mathrm{id}$; here $\sigma_T^*\mathcal{O}_{X_T}(D)$ means the pullback of
the corresponding quotient of the ideal sheaf, equivalently the fibre of
$\mathcal{O}(D)$ along $\sigma_T$), we get

$$
(m\times\mathrm{id})^*\mathcal{L}_H\cong\mathcal{O}_{X_T}(D)\otimes f_T^*\mathcal{N}
\cong\mathcal{L}\otimes f_T^*\mathcal{N}^{-1}\otimes f_T^*\mathcal{N}\cong\mathcal{L}.
$$

Thus $(m\times\mathrm{id})^*\mathcal{L}_H\in F(T)$ (as $\mathcal{L}\in F(T)$ and $F$ is a
subfunctor, the restriction of $\mathcal{L}_H$ along the morphism $(m\times\mathrm{id})$
of schemes over $H$ is in $F(T)$ if and only if $m$ factors through the
open $W$ of [lem-pc-flat-rf-open], by the characterization in
[def-pc-subfunctor] for the pair $(H,\mathcal{L}_H)$ and the explicit
description of $W$ given above), so $m$ factors through $W$; we still
write $m:T\to W$.

*$\psi$ is bijective on points, with inverse
$\theta:\mathcal{L}\mapsto m$.* The two maps are natural in $T$ (all constructions
commute with base change: pullback of divisors and their modules along
$T'\to T$ by [lem-pc-recd-pullback] and [lem-pc-rf-base-change-flat-module];
the universal object property of [def-pc-hilb-functor] and the
uniqueness of the classifying morphism of [lem-pc-cartier-criterion]
give functoriality of $m$). The composite
$h_W(T)\to F(T)\to h_W(T)$, $m\mapsto(m\times\mathrm{id})^*\mathcal{L}_H\mapsto m'$: the
adjoint section of $(m\times\mathrm{id})^*\mathcal{L}_H$ is the pullback of the adjoint
section of $\mathcal{L}_H$ ([lem-pc-universal-adjoint-section], whose zero
scheme is $D_{\mathrm{univ}}$, and [lem-pc-zero-scheme-recd]), so the
zero scheme of the adjoint section of
$(m\times\mathrm{id})^*\mathcal{L}_H$ is $D=(m\times\mathrm{id})^{-1}(D_{\mathrm{univ}})$, and
$m'$ is exactly the morphism classifying $D$, i.e. $m'=m$ by the
uniqueness in the universal property. The other composite
$\theta\circ\psi=\mathrm{id}$ on $F(T)$ was computed above
($(m\times\mathrm{id})^*\mathcal{L}_H\cong\mathcal{L}$). Hence $\psi$ is an isomorphism of
functors $h_W\cong F$, i.e. $F$ is representable (by the open subscheme
$W$ of $H$, which is a scheme: open subschemes of schemes are schemes).
