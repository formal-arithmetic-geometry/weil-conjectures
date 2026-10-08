+++
id = "lem-mg-composition-series-exists"
kind = "lemma"
title = "Existence of a composition series"
order = 2541
uses = ["def-mg-weil-composition-series"]
+++
Every nonzero finite-dimensional Weil representation has a
composition series.

## Proof

We argue by induction on $\dim V$. If $V$ is simple in the sense of
[def-mg-weil-composition-series], then $0\subsetneq V$ is a composition
series. Otherwise choose a nonzero proper Weil-stable subspace
$U\subsetneq V$. Both $U$ and $V/U$ have smaller dimension, so the
induction hypothesis gives composition series for them. Taking inverse
images in $V$ of the terms in the series for $V/U$, and placing these
after the series for $U$, gives a series of the form required in
[def-mg-weil-composition-series].
