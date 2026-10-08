+++
id = "pqf-lem-qf-locqf-qc"
kind = "lemma"
title = "Quasi-finite = locally quasi-finite + quasi-compact"
order = 200
uses = ["def-weil-pbc-scheme-conventions", "pqf-def-quasifinite"]
+++
Let $f:X\to S$ be a morphism of schemes. Then $f$ is quasi-finite if
and only if $f$ is locally quasi-finite and quasi-compact.

## Proof

A quasi-finite morphism is of finite type, hence locally of finite type
and quasi-compact, by [pqf-def-quasifinite] and
[def-weil-pbc-scheme-conventions], and each of its points is
isolated in its fibre, which is exactly quasi-finiteness at that point,
so it is locally quasi-finite. Conversely, if $f$ is locally
quasi-finite and quasi-compact, then it is locally of finite type by
[pqf-def-quasifinite] and hence of finite type by
[def-weil-pbc-scheme-conventions]; the points of $X$ are isolated
in their fibres because quasi-finiteness at a point is the isolation
condition of the definition, so $f$ is quasi-finite.
