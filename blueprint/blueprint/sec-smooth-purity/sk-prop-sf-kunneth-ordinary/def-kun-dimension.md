+++
id = "def-kun-dimension"
kind = "definition"
title = "Dimension"
order = 1674
uses = ["def-kun-support", "def-weil-pbc-scheme-conventions"]
+++
The *Krull dimension* $\kundim X$ of a scheme is the supremum
of the integers $r$ such that there is a strict chain
$Z_0\subsetneq\cdots\subsetneq Z_r$ of nonempty irreducible closed
subsets of $|X|$. For $x\in X$, the *dimension at $x$* is

$$
\kundim_xX=\min\{\kundim U:x\in U\subseteq X\text{ open}\}.
$$

For a scheme $X$ of finite type over a field $K$ the finiteness
$\kundim X<\infty$ is recorded with the other properties of this notion, and the
computation of the dimension at a point $x\in X$ in terms of the
transcendence degree of
[def-kun-support] is [lem-kun-dimension-formula].
