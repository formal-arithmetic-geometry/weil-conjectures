+++
id = "def-weil-rationalization-karoubi"
kind = "definition"
title = "Rationalization (scalar localization)"
order = 1460
uses = ["def-weil-derived-complete-integral-detailed", "def-weil-derived-tensor", "def-weil-finite-field-fiber", "def-weil-finite-torsion-constructibility"]
+++
For the global finite-field datum [def-weil-finite-field-fiber], fix a prime
$\ell\neq p$, a finite extension $E/\Ql$, a scheme $Y$, and a uniformizer
$\varpi_E$ of its valuation ring $\mathcal O_E$. The derived-complete
integral category [def-weil-derived-complete-integral-detailed] is
$D^b_c(Y,\mathcal O_E)$, built from the finite-torsion coefficients
[def-weil-finite-torsion-constructibility] $A_{E,n}=\mathcal
O_E/\varpi_E^n$. If $\mathcal C$ is an $\mathcal O_E$-linear triangulated
category, its rationalization $\mathcal C[1/\varpi_E]$ has the same objects
and, for $K,L\in\mathcal C$,

$$
 \Hom_{\mathcal C[1/\varpi_E]}(K,L)
 =\Hom_{\mathcal C}(K,L)\otimes_{\mathcal O_E}E.
$$

Set

$$
 D^b_c(Y,E)=
 D^b_c(Y,\mathcal O_E)[1/\varpi_E].
$$

No Karoubi (idempotent) completion is taken in this definition: the notation
$\mathcal C[1/\varpi_E]$ denotes the raw scalar localization displayed above,
in which no idempotent is formally adjoined. For $E=\Ql$, this uses $\mathcal
O_E=\Zl$ and $\varpi_E=\ell$.

If $E\subset L$ is a finite extension, the scalar-extension functor is

$$
 -\otimes_E L:D^b_c(Y,E)\longrightarrow D^b_c(Y,L),
$$

defined on integral representatives by completed derived tensor product
[def-weil-derived-tensor] with $\mathcal O_L$, levelwise modulo powers of the
two uniformizers, followed by rationalization.
