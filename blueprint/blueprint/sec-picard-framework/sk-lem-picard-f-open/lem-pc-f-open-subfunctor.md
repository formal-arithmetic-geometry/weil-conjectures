+++
id = "lem-pc-f-open-subfunctor"
kind = "lemma"
title = "$F$ is an open subfunctor"
order = 824
uses = ["def-pc-derived-category", "def-pc-f-subfunctor", "def-pc-pic-sigma-functor", "def-pc-subfunctor", "def-sc-invertible-module", "lem-pc-flat-rf-open", "lem-pc-rf-base-change-flat-module", "lem-pc-smooth-flat"]
lean = ["AlgebraicGeometry.isOpenImmersion_picardFunctorInvertibleDirectImage_ι"]
+++
(Picard Schemes of Curves, Lemma 44.6.2, Tag
[0B9V](https://stacks.math.columbia.edu/tag/0B9V).)
Let $k$ be a field, let $X$ be a
smooth projective curve over
$k$ with a $k$-rational point $\sigma$, and let
$F\subseteq\operatorname{Pic}_{X/k,\sigma}$ be the
subfunctor

$$
F(T):=\{\mathcal{L}\in\operatorname{Pic}_{X/k,\sigma}(T):Rf_{T,*}\mathcal{L}\text{ is isomorphic to an
invertible }\mathcal{O}_T\text{-module placed in degree }0\}.
$$

Then $F$ is a subfunctor of $\operatorname{Pic}_{X/k,\sigma}$ and the inclusion
$F\subseteq\operatorname{Pic}_{X/k,\sigma}$ is
representable by open immersions.

## Proof

$F$ is a subfunctor: if $\mathcal{L}\in F(T)$ and $u:T'\to T$ is a morphism, then
$\mathcal{L}_{T'}=u_X^*\mathcal{L}$ satisfies
$Rf_{T',*}\mathcal{L}_{T'}\cong Lu^*(Rf_{T,*}\mathcal{L})$ (base change, [lem-pc-rf-base-change-flat-module];
the morphism $f_T:X_T\to T$ is proper of finite presentation, being the
base change of $X\to\operatorname{Spec} k$, and $\mathcal{L}$ is of finite presentation and
flat over $T$: $\mathcal{L}$ is locally free, $f_T$ is smooth hence flat
[lem-pc-smooth-flat], and flat morphisms compose, so $\mathcal{L}$ is flat
over $T$), so $Rf_{T',*}\mathcal{L}_{T'}\cong u^*\mathcal{N}[0]\cong(u^*\mathcal{N})[0]$ with
$u^*\mathcal{N}$ invertible, i.e. $\mathcal{L}_{T'}\in F(T')$.

It remains to verify the open-immersion property of
[def-pc-subfunctor]. Apply [lem-pc-flat-rf-open] with
$f=f_T:X_T\to T$, $\mathcal{F}=\mathcal{L}$, $i=0$, $r=1$: there is an open $U\subseteq T$
such that a morphism $u:T'\to T$ factors through $U$ if and only if
$Rf_{T',*}\mathcal{L}_{T'}$ is isomorphic to a finite locally free
$\mathcal{O}_{T'}$-module of rank $1$ placed in degree $0$, i.e. if and only if
$u^*\mathcal{L}\in F(T')$ (a finite locally free module of rank $1$ is an
invertible module, [def-sc-invertible-module]). Taking $U=U_\xi$
for $\xi=\mathcal{L}$ gives exactly the property required.
