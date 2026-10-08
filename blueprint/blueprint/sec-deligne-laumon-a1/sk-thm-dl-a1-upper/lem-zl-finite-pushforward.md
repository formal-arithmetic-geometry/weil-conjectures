+++
id = "lem-zl-finite-pushforward"
kind = "lemma"
title = "Finite pushforward preserves upper weights"
order = 2789
uses = ["def-weil-complex-weights", "def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions", "def-weil-punctual-weights", "lemma-weil-pbc-finite-direct-image-exact", "lemma-weil-pbc-finite-stalk-formula", "prop-functor-package"]
+++
If $g:Z_0\to Y_0$ is finite and
$K\in D_{\le w}(Z_0)$, then $Rg_*K=Rg_!K$ belongs to
$D_{\le w}(Y_0)$.

## Proof

A finite morphism is proper, so $Rg_!=Rg_*$ by the properness law of
[prop-functor-package], and $g_*$ is exact by
[lemma-weil-pbc-finite-direct-image-exact]; hence
$\mathcal H^j(Rg_*K)=g_*\mathcal H^j(K)$. Fix $j$ and choose a
finite Weil filtration of $\mathcal H^j(K)$ whose nonzero quotients
$\mathcal Q_i$ are punctually pure in the sense of
[def-weil-punctual-weights], of weights $u_i\le w+j$, as
provided by [def-weil-complex-weights]. Exactness pushes this
filtration forward. It remains to check that $g_*\mathcal Q_i$ is
punctually pure of weight $u_i$. Let $y$ be closed and use the finite
stalk formula of [lemma-weil-pbc-finite-stalk-formula]. The geometric
Frobenius permutes the finitely many points $x$ over $y$; on an orbit
of length $f$, its $f$-th power on the corresponding summand is the
local Frobenius $F_x$. If $\mu$ is an eigenvalue on that orbit, then
$\mu^f$ is an eigenvalue of $F_x$. Since $\mathcal Q_i$ is pure,

$$
|\iota(\mu)|^f=|\iota(\mu^f)|
=q_x^{u_i/2}=(q_y^f)^{u_i/2},
$$

so $|\iota(\mu)|=q_y^{u_i/2}$. Thus each $g_*\mathcal Q_i$ is
punctually pure of weight $u_i$, and the pushed-forward filtration makes
$g_*\mathcal H^j(K)$ mixed of weights at most $w+j$. This holds for
every $j$, hence $Rg_*K\in D_{\le w}(Y_0)$ by
[def-weil-complex-weights].
