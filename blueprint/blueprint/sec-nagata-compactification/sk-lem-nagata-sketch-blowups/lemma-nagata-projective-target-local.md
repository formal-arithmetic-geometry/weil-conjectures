+++
id = "lemma-nagata-projective-target-local"
kind = "lemma"
title = "Properness is local on the target"
order = 88
lean = ["AlgebraicGeometry.IsProper.instIsZariskiLocalAtTarget"]
+++
Let $f\colon Y\to X$ be a morphism. If $X$ has an open cover
$(V_i)$ such that every $f^{-1}(V_i)\to V_i$ is proper, then $f$ is
proper.

## Proof

Properness is a Zariski-local property on the target. Apply the verified
target-locality instance
`AlgebraicGeometry.IsProper.instIsZariskiLocalAtTarget` to the open
cover $(V_i)$; its local hypotheses are exactly the properness hypotheses in
the statement, and it returns that $f$ is proper.

*Warning.* The analogous assertion with ``projective'' in place of
``proper'' is false for the finite-projective-space definition used here;
see Stacks Project Tag 08J0. No projectivity conclusion is used below.
