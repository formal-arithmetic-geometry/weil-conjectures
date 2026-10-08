+++
id = "def-asd-vector-bundle-zero-section"
kind = "definition"
title = "Vector bundle with zero section"
order = 1968
uses = ["def-amb-finite-locally-free-module", "def-weil-scheme-morphism-properties"]
+++
Let $S$ be a Noetherian scheme and let $\mathcal E$ be a
locally free sheaf of
$\mathcal O_S$-modules of constant finite rank $d$.
Its vector bundle is the relative affine scheme

$$
\pi:E=\operatorname{Spec}_S(\operatorname{Sym}^{\bullet}\mathcal E)
\longrightarrow S.
$$

Here the symmetric algebra is formed on each open affine and the
associated affine schemes glue by restriction. The augmentation
$\operatorname{Sym}^{\bullet}\mathcal E\to\mathcal O_S$
defines its closed
zero section $z:S\hookrightarrow E$.
A trivialization on a Zariski open $V\subset S$ is a choice
$\mathcal E|_V\cong\mathcal O_V^d$, giving
$E|_V\cong\mathbf A^d_V$. Changes of trivialization are invertible
$d$-by-$d$ matrices of regular functions on overlaps.
