+++
id = "def-pc-base-change"
kind = "definition"
title = "Base change along $T$, geometric fibres"
order = 451
uses = ["def-pc-morphism-conventions", "def-pc-scheme"]
+++
Let $f:X\to S$ be a morphism of schemes and let $T$ be a scheme over
$S$. The *base change* is

$$
X_T:=X\times_ST,\qquad
\mathrm{pr}_T:X_T\longrightarrow T,\qquad
f_T:X_T\longrightarrow X,
$$

with the projections; for $g:T'\to T$ the *base change of a
module* $\mathcal{F}$ on $X_T$ is $\mathcal{F}_{T'}=g_X^*\mathcal{F}$ where
$g_X:X_{T'}\to X_T$. For a point $t\in T$ the *fibre*
$X_t=X\times_S\operatorname{Spec}(\kappa(t))$ and the *geometric fibre* $X_{\bar t}$ are as in
Definition def:weil-pbc-scheme-conventions.
If $f$ has a section $\sigma:S\to X$ and $T$ is over $S$, then
$\sigma_T:=(\mathrm{id}_T\times\sigma):T\to X_T$ is the induced section.
