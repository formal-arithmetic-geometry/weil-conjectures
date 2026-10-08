+++
id = "lem-pc-pic-exact"
kind = "lemma"
title = "Exactness of the Picard sequence"
order = 814
uses = ["def-pc-fppf-site", "def-pc-picard-functor", "def-sc-invertible-module", "def-sc-picard-group", "lem-pc-fpqc-descent"]
+++
(Picard Schemes of Curves, Lemma 44.4.2, Tag
[0B9M](https://stacks.math.columbia.edu/tag/0B9M).)
Let $f:X\to S$ be a morphism of schemes as in
Definition [def-pc-picard-functor].
If $\mathcal{O}_T\to f_{T,*}\mathcal{O}_{X_T}$ is an isomorphism for all
$T\in\operatorname{Ob}((\mathit{Sch}/S)_{fppf})$, then

$$
0\;\longrightarrow\;\operatorname{Pic}(T)\;\longrightarrow\;\operatorname{Pic}(X_T)\;
\longrightarrow\;\operatorname{Pic}_{X/S}(T)
$$

is an exact sequence for all $T$ (the first map is $f_T^*$, the second the
canonical map).

## Proof

By base change we may assume $T=S$. *Injectivity.* Let $\mathcal{N}$ be an
invertible $\mathcal{O}_S$-module with $f^*\mathcal{N}\cong\mathcal{O}_X$. Then
$f_*f^*\mathcal{N}\cong f_*\mathcal{O}_X\cong\mathcal{O}_S$ by hypothesis. The canonical map
$\mathcal{N}\to f_*f^*\mathcal{N}$ is locally an isomorphism (the composition with
$\mathcal{O}_S\to f_*f^*\mathcal{O}_S$ is the identity of $\mathcal{O}_S$), and the composite
$\mathcal{N}\to f_*f^*\mathcal{N}\to\mathcal{O}_S$ is therefore an isomorphism; so $\mathcal{N}$ is
trivial, and $f_S^*$ is injective.

*Kernel equals image.* Let $\mathcal{L}$ be an invertible $\mathcal{O}_X$-module
whose image in $\operatorname{Pic}_{X/S}(S)$ is trivial. Since $\operatorname{Pic}_{X/S}$ is the
fppf sheafification of $T\mapsto\operatorname{Pic}(X_T)$, there is an fppf covering
$\{S_i\to S\}$ such that $\mathcal{L}|_{X_{S_i}}\cong\mathcal{O}_{X_{S_i}}$; choose
trivializing sections $s_i$ of $\mathcal{L}|_{X_{S_i}}$. Then $\mathrm{pr}_0^*s_i$ and
$\mathrm{pr}_1^*s_j$ are both trivialising sections of $\mathcal{L}$ on
$X_{S_i\times_SS_j}$, so they differ by a multiplicative unit

$$
f_{ij}\in\Gamma(X_{S_i\times_SS_j},\mathcal{O}^*)
=\Gamma(S_i\times_SS_j,\mathcal{O}^*)
$$

(the equality is the isomorphism $\mathcal{O}_T\to f_{T,*}\mathcal{O}_{X_T}$ and its
inverse on global sections, applied to
$T=S_i\times_SS_j$). The $f_{ij}$ satisfy the cocycle condition on
$S_i\times_SS_j\times_SS_k$, hence define a descent datum on invertible
sheaves for the fppf (in particular fpqc) covering
$\{S_i\to S\}$; by [lem-pc-fpqc-descent] there is an invertible
$\mathcal{O}_S$-module $\mathcal{N}$ with trivializations over $S_i$ whose associated
descent datum is $\{f_{ij}\}$. Then $f^*\mathcal{N}\cong\mathcal{L}$, as both are
invertible modules with the same descent datum for the covering
$\{X_{S_i}\to X\}$ (the pullback of the covering; base changes of fppf
coverings are fppf coverings), which shows the kernel is contained in the
image of $f_S^*$; the reverse inclusion is immediate, since the composite
$\operatorname{Pic}(S)\xrightarrow{f_S^*}\operatorname{Pic}(X)\to\operatorname{Pic}_{X/S}(S)$ vanishes on the
fppf covering $\{S_i\to S\}$ (the restrictions of the pulled-back module
are trivial). This proves the lemma.
