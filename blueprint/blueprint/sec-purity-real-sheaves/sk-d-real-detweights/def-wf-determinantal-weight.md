+++
id = "def-wf-determinantal-weight"
kind = "definition"
title = "Determinantal weight"
order = 2634
uses = ["def-mg-determinant-line", "def-weil-punctual-weights", "lem-wf-determinantal-weight-coefficient-field", "lem-wf-determinantal-weight-exists"]
+++
Let $X_0$ be a normal geometrically connected curve over $k_0$, fix
$\iota:\Qlb\xrightarrow{\sim}\mathbf C$, and let $\mathcal V$ be an
irreducible lisse Weil sheaf of rank $r$. Choose a finite coefficient
field over which its representation is defined, and let $a$ be the
weight of [lem-wf-determinantal-weight-exists], so that the
determinant line
$\det(\mathcal V)$ is
punctually $\iota$-pure of weight
$a$. The *determinantal weight* of $\mathcal V$ is

$$
\dw_\iota(\mathcal V):=\frac{a}{r}.
$$

That this number does not depend on the chosen finite coefficient field is
[lem-wf-determinantal-weight-coefficient-field]. We use the same
notation for the associated representation $V$.
