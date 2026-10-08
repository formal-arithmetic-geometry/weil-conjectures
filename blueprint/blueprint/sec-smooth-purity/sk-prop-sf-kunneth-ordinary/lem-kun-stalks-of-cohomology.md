+++
id = "lem-kun-stalks-of-cohomology"
kind = "lemma"
title = "Stalks of cohomology sheaves"
order = 1702
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-geometric-stalks", "lem-kun-stalk-as-pullback", "prop-weil-pbc-geometric-stalks-exact"]
+++
For $Q\in D(T_{\Et})$ and a geometric point $\bar t$ of $T$,

$$
\mathcal H^q(Q)_{\bar t}=\mathcal H^q(Q_{\bar t}),
$$

where $Q_{\bar t}$ denotes the pullback of $Q$ to the point.

## Proof

Choose a K-injective (or any) representative
$\mathcal Q^\bullet$ of $Q$; the stalk of the $q$-th cohomology
sheaf of $\mathcal Q^\bullet$ is the $q$-th cohomology of the
stalked complex, because the stalk functor is exact by
[prop-weil-pbc-geometric-stalks-exact] so it commutes with
kernels and images of the differentials. By
[lem-kun-stalk-as-pullback] the stalked complex is
$Q_{\bar t}$, which is the assertion.
