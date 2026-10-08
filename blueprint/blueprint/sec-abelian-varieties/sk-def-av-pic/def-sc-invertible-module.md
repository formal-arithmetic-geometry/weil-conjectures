+++
id = "def-sc-invertible-module"
kind = "definition"
title = "Invertible modules and their duals"
lean = ["AlgebraicGeometry.Scheme.Modules.IsInvertible"]
order = 442
+++
Let $X$ be a scheme (for instance a curve $C$ as in [def-sc-curves],
in which case one speaks of invertible $\mathcal O_C$-modules). An
*invertible $\mathcal O_X$-module* is a quasi-coherent
$\mathcal O_X$-module $\mathcal L$ which is locally free of rank
one for the Zariski topology (equivalently: there is an
$\mathcal O_X$-module $\mathcal L^{-1}$ with
$\mathcal L\otimes\mathcal L^{-1}\cong\mathcal O_X$). Its
*dual* is

$$
\mathcal L^{\vee}:=\mathcal{H}om_{\mathcal O_X}(\mathcal L,\mathcal O_X).
$$
