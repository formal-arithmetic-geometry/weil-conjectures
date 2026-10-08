+++
id = "def-wf-arithmetic-monodromy-extension"
kind = "definition"
title = "Arithmetic monodromy extension"
order = 2503
uses = ["def-wf-geometric-monodromy-group", "def-wf-weil-group", "lem-wf-conjugation-geometric-monodromy"]
+++
Choose $s\in W(X_0)$ with $\deg(s)=1$, and let
$\alpha(h)=\rho(s)h\rho(s)^{-1}$ be the automorphism of
$H_{\mathrm{geom}}$ furnished by
[lem-wf-conjugation-geometric-monodromy]. Define the locally
finite-type group scheme

$$
G_{\mathrm{arith}}(\rho)=
\bigsqcup_{m\in\mathbf Z}H_{\mathrm{geom}}\times\{m\},
\qquad (h,m)(h',n)=(h\alpha^m(h'),m+n),
$$

a disjoint union of finite-type pieces, with *degree map*

$$
\deg_G:G_{\mathrm{arith}}(\rho)(\overline{\mathbf Q}_\ell)
\longrightarrow\mathbf Z,\qquad (h,m)\longmapsto m.
$$

That the displayed multiplication is a group law, and that $\deg_G$ is
then a group homomorphism, The
map to matrices is $(h,m)\mapsto h\rho(s)^m$. This map need not be
injective: the integer in the second coordinate is deliberately retained,
because it records the Weil degree even when two degree components have the
same matrix image.
