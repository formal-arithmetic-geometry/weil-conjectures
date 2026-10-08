+++
id = "lem-mg-normal-restriction-semisimple"
kind = "lemma"
title = "Restriction of a semisimple representation to a normal subgroup"
order = 2518
uses = ["def-wf-geometric-semisimplicity", "def-wf-semisimple-module", "def-wf-simple-module"]
+++
Let $N\triangleleft\Gamma$ be a normal subgroup, with no finiteness
assumption on $\Gamma/N$. Every finite-dimensional semisimple
$\Gamma$-representation over $\Qlb$ restricts to a semisimple
$N$-representation. In particular, a semisimple Weil representation is
geometrically semisimple.

## Proof

By the direct-sum definition of semisimplicity in
[def-wf-semisimple-module], it is enough to treat a simple
$\Gamma$-module $V$. Choose a nonzero $N$-stable subspace
$S\subseteq V$ of least positive dimension. It is simple as an
$N$-module by [def-wf-simple-module]. Normality makes every
translate $\gamma S$ another simple $N$-submodule. The sum of all
these translates is a nonzero $\Gamma$-submodule, hence is $V$, and
finitely many translates already span because $V$ is finite-dimensional.

Add those translates one at a time. If $D$ is the direct sum already
obtained and $S'$ is the next translate, then $S'\cap D$ is an
$N$-submodule of the simple module $S'$; it is either zero, in which
case $D+S'=D\oplus S'$, or all of $S'$, in which case nothing is
added. Thus $V|_N$ is a direct sum of simple $N$-modules. For a Weil
representation take $N=\pi_1(X)$, which is normal in the Weil group;
the final assertion is precisely geometric semisimplicity in
[def-wf-geometric-semisimplicity].
