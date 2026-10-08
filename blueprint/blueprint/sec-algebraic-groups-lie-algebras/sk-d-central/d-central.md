+++
id = "d-central"
kind = "definition"
title = "Positive central pairs"
order = 2525
uses = ["d-monodromy"]
lean = ["AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.IsPositiveCentralPair"]
+++
For the monodromy data $(G,H,F)$ of a represented degree datum
([d-monodromy]), a positive central pair is
$(N,z)$ with $N\in\mathbf Z_{>0}$ and
$z\in Z(G)\cap HF^N$, where $Z(G)$ is the centre of $G$.
The coset condition does not assert that $G/H$ is infinite cyclic or
that the cosets $HF^N$ for different $N$ are distinct.

Uses: [d-monodromy]
