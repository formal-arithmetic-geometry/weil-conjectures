+++
id = "def-pod-trace-cup-reading"
kind = "definition"
title = "Poincare duality conventions: trace and trace-cup pairing"
order = 2422
uses = ["cor-cbc-proper-coincidence", "def-pod-conventions", "def-pur-smooth-trace", "def-weil-poincare-trace-cup"]
+++
In the conventions of [def-pod-conventions] ($X_0$ not necessarily
proper), the trace map of [def-weil-poincare-trace-cup] is read through the
canonical orientation $\eta_X$ as the counit of $Ra_{X!}\dashv Ra_X^!$,

$$
\operatorname{tr}_X:H_c^{2d}(X,\Lambda(d))\longrightarrow\Lambda,
\qquad
\operatorname{tr}^{(-d)}_X:H_c^{2d}(X,\Lambda)\longrightarrow\Lambda(-d),
$$

the second being its untwisted form; neither uses properness (compare
[def-pur-smooth-trace], where the same trace is realized as the normalized
smooth trace $\operatorname{Tr}^{\mathrm{sm}}_{a_X,\Lambda}$). If $X_0$ is
proper, then $Ra_{X!}\cong Ra_{X*}$ by [cor-cbc-proper-coincidence], so
$H_c^{2d}=H^{2d}$ and $\operatorname{tr}^{(-d)}_X$ is the map
$H^{2d}(X,\Lambda)\to\Lambda(-d)$ of [def-weil-poincare-trace-cup]; only
in this case is the trace–cup pairing
$\langle x,y\rangle_i=\operatorname{tr}^{(-d)}_X(x\smile y)$ on
$H^i(X,\Lambda)\times H^{2d-i}(X,\Lambda)$ of that definition read in
these conventions.
