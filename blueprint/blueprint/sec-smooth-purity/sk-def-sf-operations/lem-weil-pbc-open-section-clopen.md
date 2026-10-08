+++
id = "lem-weil-pbc-open-section-clopen"
kind = "lemma"
title = "An open section is also closed"
order = 1477
uses = ["def-weil-pbc-scheme-conventions", "lem-weil-pbc-closed-immersion-from-composite"]
+++
Let $p:V\to S$ be a
separated morphism and
$s:S\hookrightarrow V$ an
open immersion satisfying
$p\circ s=\operatorname{id}_S$. Its image is open and closed in
$V$, and the decomposition
$V=s(S)\amalg(V\setminus s(S))$ is a decomposition into open
subschemes.

## Proof

The identity of $S$ is a closed immersion, so
[lem-weil-pbc-closed-immersion-from-composite] makes $s$ a
closed immersion. It is already an open immersion; the two immersion
notions of [def-weil-pbc-scheme-conventions] therefore identify
$S$ with an open and closed subscheme of $V$. Its complement is
open, and the two disjoint opens cover $V$.
