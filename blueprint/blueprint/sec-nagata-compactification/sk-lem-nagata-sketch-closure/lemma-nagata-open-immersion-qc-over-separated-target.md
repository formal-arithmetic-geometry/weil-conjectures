+++
id = "lemma-nagata-open-immersion-qc-over-separated-target"
kind = "lemma"
title = "Quasi-compactness of an open map to a separated target"
order = 79
lean = ["AlgebraicGeometry.QuasiCompact.of_comp"]
uses = ["lemma-nagata-finite-type-to-separated-target"]
+++
Let $T\to Y\to B$ be a commutative triangle. Assume that $T\to B$ is
of finite type, that $Y\to B$ is separated, and that $T\to Y$ is an
open immersion. Then $T\to Y$ is a quasi-compact open immersion.

## Proof

By [lemma-nagata-finite-type-to-separated-target], the open immersion
is of finite type. An open immersion is locally of finite type, and it is
of finite type exactly when it is quasi-compact.
