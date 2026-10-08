+++
id = "rem-dl-a1-conventions"
kind = "remark"
title = "Affine-line and weight conventions"
order = 2723
uses = ["def-weil-frobenius-detailed", "def-weil-punctual-weights", "def-wf-middle-extension", "def-wf-tate-twist"]
lean = ["AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant", "AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity"]
+++
Fix $k_0=\mathbf F_q$, its algebraic closure $k$, a prime $\ell\ne \operatorname{char}(k_0)$, and $\iota:\DLAQ\simeq\mathbf C$. Write
$A_0=\mathbf A^1_{k_0}$, $A=A_0\otimes k$, and use a prime to denote the
dual affine line. All cohomology is geometric, with geometric Frobenius
([def-weil-frobenius-detailed]).
A lisse Weil sheaf is *pure of weight $w$* if every eigenvalue
$\alpha$ at a closed point $x$ satisfies
$|\iota\alpha|=q_x^{w/2}$; replace equality by $\leq$ for an upper bound
([def-weil-punctual-weights]).
The twist $(-1)$ raises weights by two ([def-wf-tate-twist]).

For a dense open $j:U_0\hookrightarrow A_0$, $j_*F$ denotes the
*ordinary* sheaf direct image. Its stalks at missing points are
inertia invariants; its curve perverse intermediate extension is
$j_{!*}(F[1])=(j_*F)[1]$ ([def-wf-middle-extension]). Unramifiedness at infinity means that inertia
at $\infty\in\mathbf P^1_k$ acts trivially on the geometric generic fiber.
A geometrically constant sheaf has trivial geometric fundamental-group
action, while its Frobenius module may be nontrivial.
