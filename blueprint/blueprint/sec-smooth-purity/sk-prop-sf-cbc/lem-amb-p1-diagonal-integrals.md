+++
id = "lem-amb-p1-diagonal-integrals"
kind = "lemma"
title = "The two integrals of the diagonal class"
order = 1572
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-amb-p1-trace", "def-coefficient-twists-detailed", "def-sc-p1-standard", "lem-amb-cartier-kummer-map", "thm-amb-p1-decomposition"]
+++
Put $W=P\times_SP$, let $p_1,p_2:W\to P$ be
the projections, and let $\Delta:P\hookrightarrow W$
be the diagonal. Its Cartier Kummer map
$\delta:\Delta_*A_P\to A_W(1)[2]$ satisfies, for
$a=1,2$,

$$
A_P=R(p_a)_*\Delta_*A_P
\xrightarrow{R(p_a)_*\delta}R(p_a)_*A_W(1)[2]
\xrightarrow{t_{p_a}} A_P
=\operatorname{id}_{A_P}.
$$

The notation refers to the projective line, projective-line integration, and Tate twists.

## Proof

The equation $x_0y_1-x_1y_0=0$ shows that $\Delta$
is an effective Cartier divisor. For either projection it is
a section. Apply [lem-amb-cartier-kummer-map].
Under [cor-weil-pbc-geometric-fiber-finite], the displayed
endomorphism restricts at every geometric point of $P$ to
integration of the class of a single rational point of
$\mathbf P^1$. Its associated line bundle has degree one,
so [thm-amb-p1-decomposition], [def-amb-p1-trace] make this
value $1$. An endomorphism of the sheaf $A_P$, placed
in degree zero, is determined by its stalks. Hence the
displayed endomorphism is the identity for both projections.
