+++
id = "pqf-lem-finite-qf"
kind = "lemma"
title = "Finite morphisms are quasi-finite"
order = 530
uses = ["def-weil-pbc-scheme-conventions", "pqf-def-quasifinite", "pqf-lem-qf-finitefibres"]
+++
A finite morphism of
schemes is quasi-finite.

## Proof

A finite morphism is affine and $f_*\mathcal O_X$ is a finite
$\mathcal O_S$-algebra, so $f$ is of finite type and quasi-compact, by
[def-weil-pbc-scheme-conventions]. Its fibres are finite: the
fibre at $s$ is $\operatorname{Spec}$ of a finite
$\kappa(s)$-algebra, which is a finite-dimensional $\kappa(s)$-vector
space, hence Artinian and therefore has finitely many prime ideals
(classical algebra). A morphism of finite type with finite fibres is
quasi-finite, by [pqf-lem-qf-finitefibres], if it is locally of
finite type; and it is, because finite type implies locally of finite
type in the sense of [pqf-def-quasifinite].
