+++
id = "lem-pc-sigma-subfunctor"
kind = "lemma"
title = "$\\operatorname{Pic}_{X/k,\\sigma}$ is a subfunctor of the Picard presheaf"
order = 800
uses = ["def-pc-base-change", "def-pc-pic-sigma-functor", "def-pc-picard-presheaf", "def-pc-rational-point", "def-pc-subfunctor", "def-sc-picard-group"]
+++
Let $k$ be a field, $X$ a scheme over $k$ and $\sigma\in X(k)$ a
$k$-rational point. Then the
assignment

$$
T\longmapsto\operatorname{Ker}\Bigl(\sigma_T^*:\operatorname{Pic}(X_T)
\longrightarrow\operatorname{Pic}(T)\Bigr)
$$

of [def-pc-pic-sigma-functor] is a
subfunctor of the
Picard presheaf on the category of
schemes over $k$.

## Proof

The sets $\operatorname{Ker}(\sigma_T^*)$ are subsets of
$\operatorname{Pic}(X_T)$ by [def-pc-pic-sigma-functor], and
$\operatorname{Pic}(X_T)$ with its pullback maps is the Picard presheaf of
[def-pc-picard-presheaf]; it remains to check the condition of
[def-pc-subfunctor]. Let $u:T'\to T$ be a morphism of schemes over
$k$, write $u_X:X_{T'}\to X_T$ for the base change of $u$
([def-pc-base-change]) and let
$[\mathcal L]\in\operatorname{Ker}(\sigma_T^*)$. By
[def-pc-rational-point] the induced sections are
$\sigma_T=\mathrm{id}_T\times\sigma$ and
$\sigma_{T'}=\mathrm{id}_{T'}\times\sigma$; under the identification
$X_{T'}=X_T\times_TT'$ of [def-pc-base-change] the composites
$u_X\circ\sigma_{T'}$ and $\sigma_T\circ u$ are therefore both the
morphism $T'\to X_T=X\times_kT$ with components $\sigma$ and $u$.
Pullback of invertible modules
is contravariant and compatible with composition
([def-sc-picard-group]), so
$\sigma_{T'}^*\circ u_X^*=u^*\circ\sigma_T^*$ as maps on Picard groups, and
therefore

$$
\sigma_{T'}^*(u_X^*\mathcal L)\cong u^*(\sigma_T^*\mathcal L)
\cong u^*\mathcal O_T\cong\mathcal O_{T'},
$$

because $\sigma_T^*\mathcal L\cong\mathcal O_T$. Hence
$u_X^*\mathcal L\in\operatorname{Ker}(\sigma_{T'}^*)$, which is exactly
the subfunctor condition.
