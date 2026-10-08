+++
id = "lem-kun-proper-stability"
kind = "lemma"
title = "Properness survives base change and composition"
order = 1709
uses = ["def-weil-pbc-scheme-conventions", "lem-weil-pbc-proper-base-change", "lem-weil-pbc-proper-composition"]
+++
The class of proper
morphisms is stable under base change and composition (the two
instances are [lem-weil-pbc-proper-base-change] and
[lem-weil-pbc-proper-composition]); in particular, if $X\to \Spec(k)$ is proper and $Y$ is any $k$-scheme, then the projection
$\operatorname{pr}_2:X\times_kY\to Y$ is proper.

## Proof

Stability under base change is [lem-weil-pbc-proper-base-change],
and stability under composition is
[lem-weil-pbc-proper-composition]; the last assertion is the
first applied to the proper morphism $X\to\Spec(k)$ and the base
change $Y\to\Spec(k)$, the composite being the projection
$\operatorname{pr}_2:X\times_kY\to Y$.
