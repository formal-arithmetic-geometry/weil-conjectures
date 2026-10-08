+++
id = "lem-pc-section-clearing-denominators"
kind = "lemma"
title = "Clearing denominators for a section of an invertible module"
order = 625
uses = ["def-pc-morphism-conventions", "def-pc-zero-scheme", "def-sc-invertible-module", "pqf-def-coherent"]
+++
Let $X$ be a quasi-compact scheme
separated over an affine scheme,
let $\mathcal L$ be an
invertible module, and let
$s\in\Gamma(X,\mathcal L)$. Put
$X_s=X\setminus Z(s)$, the complement of its
zero scheme.
For every quasi-coherent module
$\mathcal F$ and $t\in\Gamma(X_s,\mathcal F)$, there exist $m\ge0$
and $u\in\Gamma(X,\mathcal F\otimes\mathcal L^{\otimes m})$ such that
$u|_{X_s}=t\otimes s^m$.

## Proof

Choose a finite affine cover $V_j$ of $X$ on which $\mathcal L$
is free, as in [def-sc-invertible-module]; write $e_j$ for its
basis and $s=f_je_j$. By [def-pc-zero-scheme],
$X_s\cap V_j=D(f_j)$. For
$M_j=\Gamma(V_j,\mathcal F)$, the affine description of
[pqf-def-coherent] identifies sections there with $(M_j)_{f_j}$.
Choose one $a\ge0$ so that $f_j^a t$ has a lift $t_j\in M_j$ for
every $j$. This is possible by the definition of localization and
the finiteness of the cover. The sections $t_j\otimes e_j^a$ of
$\mathcal F\otimes\mathcal L^a$ agree on the part of each overlap
where $s$ is invertible, but may not yet agree on the full overlap.

The overlaps $V_j\cap V_k$ are affine: they are inverse images of
the closed diagonal under the affine product $V_j\times V_k$ over
the affine base. On such an overlap use the trivialization $e_j$.
The difference of the two proposed sections is a module element
whose localization at $f_j$ is zero. Hence some power $f_j^{b_{jk}}$
kills that difference. There are finitely many pairs, so choose
$b\ge b_{jk}$ for all of them. Multiplying all local sections
by the global section $s^b$ makes their differences zero on every
overlap. The sheaf gluing axiom gives a section $u$ of
$\mathcal F\otimes\mathcal L^{a+b}$ on $X$, with restriction
$t\otimes s^{a+b}$ on $X_s$. Take $m=a+b$.
