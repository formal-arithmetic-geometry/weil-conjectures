+++
id = "lem-wf-finite-index-restriction-semisimple"
kind = "lemma"
title = "Restriction to a finite-index normal subgroup"
order = 2516
uses = ["def-wf-semisimple-module", "def-wf-simple-module"]
+++
Let $N\triangleleft\Gamma$ be a normal subgroup of finite index. If
$V$ is a finite-dimensional semisimple $\Gamma$-module over a field,
then its restriction to $N$ is semisimple.

## Proof

By the direct-sum definition in [def-wf-semisimple-module], it is
enough to treat a simple $\Gamma$-module $V$. Choose a nonzero
$N$-stable subspace $S\subseteq V$ of smallest positive dimension;
then $S$ is simple as an $N$-module by
[def-wf-simple-module]. Normality of $N$ implies that every
translate $\gamma S$ is again a simple $N$-submodule. The sum of
all these translates is a nonzero $\Gamma$-submodule, hence is all of
$V$. Only finitely many translates are needed because $V$ is
finite-dimensional.

Add these translates one at a time. Suppose that the translates already
chosen form a direct sum $D$, and consider another simple translate
$S'$. The intersection $S'\cap D$ is an $N$-submodule of the
simple module $S'$; it is therefore either zero, in which case
$D+S'=D\oplus S'$, or all of $S'$, in which case $S'\subseteq D$
and nothing needs to be added. The resulting finite direct sum is $V$,
so $V|_N$ is semisimple.
