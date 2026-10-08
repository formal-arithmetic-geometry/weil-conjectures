+++
id = "def-pc-finite-locally-free"
kind = "definition"
title = "Finite locally free morphisms"
order = 678
uses = ["def-pc-base-change", "def-pc-morphism-conventions", "def-weil-pbc-scheme-conventions"]
+++
Let $f:X\to S$ be a morphism of schemes. Then $f$ is *finite locally
free* if $f$ is finite, flat and locally of finite presentation. For an
integer $d\geq0$, $f$ is *finite locally free of degree $d$* if it is
finite locally free and for every $s\in S$ the fibre
$X_s=X\times_S\operatorname{Spec}\kappa(s)$ (a finite set of points)
satisfies

$$
\dim_{\kappa(s)}\Gamma(X_s,\mathcal{O}_{X_s})=d .
$$
