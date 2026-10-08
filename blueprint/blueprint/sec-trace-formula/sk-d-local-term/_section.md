+++
id = "sk-d-local-term"
kind = "section"
title = "Local terms"
order = 2335
uses = ["sk-d-corr", "sk-d-integral", "sk-d-pairing", "sk-d-six", "sk-d-trace-class"]
lean = ["AlgebraicGeometry.ProEtale.GeometricOperations.localTerm"]
+++
*Definition (sketch).*

For an opposite pair $(C,c,u),(D,d,v)$, put $E=E(C,D)$.
Let $j_B:B\hookrightarrow E$ be open and closed, with $B$ proper over $s$.
The restriction of its pairing is

$$
A_B\simeq j_B^*A_E\xrightarrow{j_B^*\langle u,v\rangle_{\mathrm{LV}}}
j_B^*\omega_E\simeq\omega_B,
$$

where the last identification uses open purity and dualizing composition.
This restricted section is defined even when $B$ is not proper;
properness is needed for the scalar integral below.
Define its local term by integration:

$$
\LT_B(u,v):=\int_B j_B^*\langle u,v\rangle_{\mathrm{LV}}\in A.
$$

For an endocorrespondence, use its trace class to set
$\LT_B(u):=\int_B j_B^*\Tr_c(u)$, with $B\subseteq\Fix(c)$; it equals
$\LT_B(u,1_K)$ because $\Tr_c(u)=\langle u,1_K\rangle_{\mathrm{LV}}$
([lem-trf-trace-class-diagonal-pairing]).
The ambient support need not be proper. At a Frobenius fixed point,
$\LT_{\bar x}$ means the local term on its reduced clopen point component.

Uses: [sk-d-corr], [sk-d-integral], [sk-d-pairing], [sk-d-six], [sk-d-trace-class]
