+++
id = "lem-sc-positive-degree-ample"
kind = "lemma"
title = "Positive degree implies ample"
order = 719
uses = ["def-sc-ample", "def-sc-curves", "def-sc-pic0", "lem-sc-degree-2g1-very-ample"]
+++
Let $C$ be a proper smooth connected curve of
genus $g$ over an algebraically closed field $k$ and
$\mathcal L$ a line bundle with $\deg\mathcal L>0$
([def-sc-pic0]). Then $\mathcal L$ is
ample.

## Proof

Since $\deg$ is a homomorphism ([def-sc-pic0]),
$\deg(\mathcal L^{\otimes m})=m\deg\mathcal L\to\infty$, so for
$m\gg0$ one has $\deg(\mathcal L^{\otimes m})\geq2g+1$, and by
[lem-sc-degree-2g1-very-ample] the bundle
$\mathcal L^{\otimes m}$ is very ample; by definition
([def-sc-ample]) $\mathcal L$ is ample.
