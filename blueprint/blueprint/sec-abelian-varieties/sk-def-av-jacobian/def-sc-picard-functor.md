+++
id = "def-sc-picard-functor"
kind = "definition"
title = "The Picard functor of a proper curve"
order = 447
uses = ["def-sc-curves", "def-sc-invertible-module", "def-sc-pic0", "def-sc-picard-group"]
+++
Let $C$ be a proper smooth connected curve over a
field $k$. The *Picard functor*

$$
\operatorname{Pic}_{C/k}:(k\text{-algebras})\longrightarrow\mathbf{Ab},
\qquad \operatorname{Pic}_{C/k}:=
\bigl(R\longmapsto\operatorname{Pic}(C\times_k\operatorname{Spec}R)\bigr)^{\#}_{\mathrm{fppf}},
$$

is the fppf sheafification of the presheaf of
invertible modules; for
$d\in\mathbf Z$, $\operatorname{Pic}^d_{C/k}$ is the subfunctor
of $\operatorname{Pic}_{C/k}$ of invertible modules of fibrewise
degree $d$ (degree $d$ on every geometric fibre). This
definition fixes the fppf sheafification and its subfunctors
$\operatorname{Pic}^d_{C/k}$, and nothing else: no
representability of $\operatorname{Pic}_{C/k}$, and no openness
or closedness of the subfunctors $\operatorname{Pic}^d_{C/k}$, is
assumed here.
