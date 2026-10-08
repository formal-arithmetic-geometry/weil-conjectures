+++
id = "lem-a1-extension-bounds"
kind = "lemma"
title = "Extension bounds for Frobenius modules"
order = 2790
uses = ["def-weil-frobenius-module-weights"]
+++
Let $0\to V'\to V\to V''\to 0$ be an exact sequence of Frobenius
modules. If $V'$ and $V''$ are mixed of weights at most $w$, then
$V$ is mixed of weights at most $w$.

## Proof

Choose the Frobenius-stable filtrations of $V'$ and $V''$ given by
[def-weil-frobenius-module-weights] (of weights at most $w$);
pull back the filtration of $V''$ along the projection
$V\to V''$ and splice it after the filtration of $V'$. The graded
pieces are the graded pieces of $V'$ and the graded pieces of
$V''$, so all their weights are at most $w$; by
[def-weil-frobenius-module-weights] the module $V$ is mixed of
weights at most $w$.
