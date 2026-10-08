+++
id = "def-exc-etale-algebra-lift"
kind = "definition"
title = "Lifting a Jacobian presentation"
order = 1836
uses = ["def-exc-jacobian-presentation"]
+++
Let $I\subset A$ be an ideal, and specify a square Jacobian presentation
[def-exc-jacobian-presentation]
$\overline B=(A/I)[x_1,\ldots,x_m]/(\overline f_1,\ldots,\overline f_m)$.
Choose coefficientwise lifts $f_i\in A[x_1,\ldots,x_m]$, put
$\Delta=\det(\partial f_i/\partial x_j)$, and define
$$
 B^{\mathrm{lift}}=
 A[x_1,\ldots,x_m,t]/(f_1,\ldots,f_m,t\Delta-1).
$$
Its map to $\overline B$ sends $t$ to $\overline\Delta^{-1}$.
