+++
id = "def-pd-fibrewise-degree"
kind = "definition"
title = "Fibrewise degree of an invertible module on a curve"
order = 841
uses = ["def-pc-base-change", "def-pc-degree-line-bundle", "def-pc-euler-characteristic", "def-pc-fppf-site", "def-pc-geometrically-irreducible", "def-pc-smooth-projective-curve", "def-sc-invertible-module"]
+++
Let $k$ be a field and let $C$ be a
smooth projective curve over $k$
which is geometrically integral.
Let $T$ be a $k$-scheme (in the fppf site of
[def-pc-fppf-site]) and let $\mathcal{L}$ be an
invertible $\mathcal{O}_{C_T}$-module,
with $C_T$ the base change of $C$ along
$T\to\Spec(k)$. For a point $t\in T$ with residue field $\kappa(t)$, the
*fibre* $\mathcal{L}_t$ is an invertible module on the proper curve
$C_{\kappa(t)}$ over the field $\kappa(t)$, and the
*fibrewise degree* of $\mathcal{L}$ at $t$ is the integer

$$
\deg_T(\mathcal{L})(t):=\deg_{C_{\kappa(t)}}\bigl(\mathcal{L}_t\bigr)
:=\chi\bigl(C_{\kappa(t)},\mathcal{L}_t\bigr)
-\chi\bigl(C_{\kappa(t)},\mathcal{O}_{C_{\kappa(t)}}\bigr),
$$

with $\chi$ the Euler characteristic and
$\deg$ the degree of an invertible module
on a proper curve over a field.
