+++
id = "sk-d-trace-class"
kind = "section"
title = "Diagonal trace class"
order = 2313
uses = ["sk-d-corr", "sk-d-pairing"]
lean = ["AlgebraicGeometry.ProEtale.GeometricOperations.traceClass"]
+++
*Definition (sketch).*

For $(X,K)$, the diagonal identity is the
endocorrespondence with support $X$, support map
$\Delta_X:X\to X\times X$, identity legs, and coefficient map $1_K$.
For another endocorrespondence $(C,c,u)$, its intersection with this
diagonal is $F=\Fix(c)$. Its trace class
$\Tr_c(u):A_F\to\omega_F$ is the Verdier trace class: the mate of $u$
followed by the trace map of external duality ([def-trf-trace-class]).
It is computed by the supported pairing:

$$
\Tr_c(u)=\langle u,1_K\rangle_{\mathrm{LV}}:A_F\longrightarrow\omega_F
$$

([lem-trf-trace-class-diagonal-pairing]; the two constructions agree
exactly, with no sign or twist).

This is a class on the specified scheme $F$; integration, when defined,
is a separate operation.

Uses: [sk-d-corr], [sk-d-pairing]
