+++
id = "cor-pqf-proper-quasifinite-finite"
kind = "theorem"
title = "Proper quasi-finite morphisms are finite"
lean = ["AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite"]
order = 547
uses = ["def-weil-pbc-scheme-conventions", "pqf-def-affine-morphism", "pqf-def-quasifinite", "pqf-lem-affine-local-target", "pqf-lem-proper-basic", "pqf-lem-qf-finitefibres", "pqf-lem-qf-locqf-qc", "thm-pqf-finite-iff-proper-finite-fibres", "thm-pqf-zmt-factorization"]
tags = ["latex:corollary"]
+++
Let $f:X\to S$ be a morphism of schemes (no hypothesis on $S$). If
$f$ is proper and quasi-finite, then $f$ is finite.
(*Stacks Project, More on Morphisms, a consequence of Zariski's main
theorem; the locally Noetherian case is Tag
[02OG](https://stacks.math.columbia.edu/tag/02OG).*)

## Proof

*Step 0: reduction to an affine base.* By
[def-weil-pbc-scheme-conventions], $f$ is finite if and only if it is
affine and $f_*\mathcal O_X$ is a finite $\mathcal O_S$-module. By
[pqf-lem-affine-local-target] (with [pqf-def-affine-morphism]) it
therefore suffices to find an affine open covering $S=\bigcup_iV_i$
such that each $f^{-1}(V_i)$ is affine with
$\Gamma(f^{-1}(V_i),\mathcal O_X)$ a finite
$\Gamma(V_i,\mathcal O_S)$-module: then $f$ is affine, $f_*\mathcal
O_X$ is the quasi-coherent sheaf whose sections over $V_i$ are these
modules, and it is of finite type on the covering $\{V_i\}$. Let
$V=\operatorname{Spec}R\subseteq S$ be any affine open and replace
$f$ by its restriction $f^{-1}(V)\to V$. This restriction is again
proper (it is the base change of $f$ along the open immersion
$V\hookrightarrow S$, and separatedness, finite type and universal
closedness are preserved, the last because a base change of the
restriction is a base change of $f$) and quasi-finite (it is of finite
type and its fibres are fibres of $f$, [pqf-def-quasifinite]). So we
may assume $S=\operatorname{Spec}R$ is affine, and we must show that
$X$ is affine with $\Gamma(X,\mathcal O_X)$ a finite $R$-module.

*Step 1: Zariski's main theorem.* By [pqf-lem-proper-basic], $f$ is
separated and of finite type; by [pqf-lem-qf-locqf-qc] it is locally
quasi-finite, i.e. quasi-finite at every point of $X$
([pqf-def-quasifinite]). The affine scheme $S$ is quasi-compact and
quasi-separated. Hence [thm-pqf-zmt-factorization] gives a scheme
$T$, a quasi-compact open immersion $j:X\hookrightarrow T$ and a
finite morphism $p:T\to S$ with $f=p\circ j$. Since $p$ is finite,
it is affine, so $T=\operatorname{Spec}B$ with $B=\Gamma(T,\mathcal
O_T)$ a finite $R$-algebra.

*Step 2: the image of $j$ is closed.* The morphism $p$ is affine,
hence separated (a morphism of affine schemes has closed-immersion
diagonal, as $B\otimes_RB\to B$ is surjective). Consider the graph
$\Gamma_j=(\mathrm{id}_X,j):X\to X\times_ST$. It is the base change of
the diagonal $\Delta_{T/S}:T\to T\times_ST$ along
$j\times\mathrm{id}_T:X\times_ST\to T\times_ST$, hence a closed
immersion, and in particular a closed map. The second projection
$\mathrm{pr}_2:X\times_ST\to T$ is the base change of $f$ along $p$;
since $f$ is universally closed ([pqf-lem-proper-basic]), it is a
closed map. Therefore $j=\mathrm{pr}_2\circ\Gamma_j$ is a closed map,
and $Z=j(X)$ is a subset of $T$ which is both open (as $j$ is an open
immersion) and closed.

*Step 3: conclusion.* An open and closed subset of the affine scheme
$\operatorname{Spec}B$ is of the form $Z=D(e)=V(1-e)$ for an
idempotent $e\in B$ (the standard correspondence between idempotents
of $B$ and open-and-closed subsets of $\operatorname{Spec}B$, via the
decomposition $B\cong eB\times(1-e)B$). Since $j$ identifies $X$ with
the open subscheme $Z=D(e)$ of $T$, we get

$$
X\cong\operatorname{Spec}B_e\cong\operatorname{Spec}\bigl(B/(1-e)B\bigr),
$$

using $B_e\cong eB\cong B/(1-e)B$ for an idempotent $e$. Thus $X$ is
affine and $\Gamma(X,\mathcal O_X)\cong B/(1-e)B$ is a quotient of the
finite $R$-module $B$, hence a finite $R$-module. By Step 0, $f$ is
finite.

*Remark (the locally Noetherian case).* When $S$ is locally
Noetherian the statement also follows without Zariski's main theorem:
a quasi-finite morphism has finite fibres by
[pqf-lem-qf-finitefibres], so $f$ is proper with finite fibres in the
sense of [pqf-def-quasifinite], and
[thm-pqf-finite-iff-proper-finite-fibres] applies.
