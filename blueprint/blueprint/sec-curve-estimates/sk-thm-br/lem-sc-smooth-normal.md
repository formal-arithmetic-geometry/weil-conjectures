+++
id = "lem-sc-smooth-normal"
kind = "lemma"
title = "Smooth schemes are normal"
order = 920
uses = ["def-sc-curves", "lem-sc-smooth-regular"]
+++
A smooth curve over a field $k$ is
normal at every point.

## Proof

By [lem-sc-smooth-regular] all local rings are regular;
regular local rings are integrally closed (they are unique
factorization domains: *reference: Stacks Project, More on
Algebra, Lemma 15.123.2,
[Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0)*), hence the
scheme is normal.
