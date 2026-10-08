+++
id = "d-monodromy"
kind = "definition"
title = "Represented degree data and monodromy"
order = 2506
uses = ["def-wf-fundamental-representation", "def-wf-geometric-monodromy-group", "def-wf-weil-group", "lem-wf-degree-component-image", "lem-wf-zariski-closure-subgroup"]
lean = ["AlgebraicGeometry.Monodromy.DegreeDatum", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.arithmeticMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.geometricMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.frobenius", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.IsSemisimple"]
+++
A degree datum consists of a group $W$, a surjective homomorphism
$\deg:W\to\mathbf Z$, and a chosen element $\gamma$ of degree $1$.
Put $P=\ker(\deg)$; every $w$ has the form $u\gamma^{\deg w}$ with
$u\in P$. A represented datum adds a representation
$\rho:W\to\operatorname{GL}(V)$. Its arithmetic and geometric monodromy groups are
the reduced Zariski closures

$$
G=\overline{\rho(W)},\qquad H=\overline{\rho(P)},\qquad F=\rho(\gamma).
$$

These names concern the degree datum only; no topology or sheaf is
required in this subsection. A semisimple datum means that $V$ is a
semisimple $W$-representation.

For the Weil representation $\rho$ of a lisse Weil sheaf
([def-wf-fundamental-representation]), $(W(X_0),\deg,s)$ with $s$ of
degree one ([def-wf-weil-group]) is a degree datum, $P=\Pi$, and $H$
is the geometric monodromy group $H_{\mathrm{geom}}$ of
[def-wf-geometric-monodromy-group]; both closures are closed subgroups
by [lem-wf-zariski-closure-subgroup]. To avoid a clash with the
arithmetic monodromy extension $G_{\mathrm{arith}}(\rho)$, the closure
$G$ is then written $G_{\mathrm{Zar}}$. The degree-$m$ part of
$\rho(W(X_0))$ has closure $H_{\mathrm{geom}}F^m$
([lem-wf-degree-component-image]), and $G_{\mathrm{Zar}}$ contains all
of these translates.
