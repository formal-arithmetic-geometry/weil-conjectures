+++
id = "lem-galois-flasque"
kind = "lemma"
title = "Flasque resolutions and the connecting map"
order = 1407
uses = ["def-weil-pbc-etale-cohomology", "def-weil-pbc-etale-sheaves"]
+++
Let $\mathcal F$ be a sheaf of abelian groups on $Y_{\Et}$. Then there
is an exact sequence of sheaves

$$
0\longrightarrow\mathcal F\longrightarrow I\xrightarrow{\ d\ }J
\longrightarrow0
$$

with $I$ flasque, $J=I/\mathcal F$ its quotient, and
$H^q(Y_{\Et},I)=0$ for $q\ge1$; consequently the connecting map induces

$$
H^1(Y_{\Et},\mathcal F)\cong\operatorname{coker}\bigl(d_Y:I(Y)\to
J(Y)\bigr).
$$

## Proof

Take the Godement construction, for sheaves on $Y_{\Et}$ in the sense
of [def-weil-pbc-etale-sheaves] and with the cohomology of
[def-weil-pbc-etale-cohomology]:
$G(\mathcal G)(U)=\prod_{u\in U}\mathcal G_u$ is a sheaf containing $\mathcal G$ and is flasque, restriction
maps being surjective because they only discard coordinates. A flasque sheaf has vanishing higher
cohomology: for $0\to\mathcal A\to\mathcal B\to\mathcal C\to0$ with
$\mathcal A$ flasque, sections of $\mathcal B$ over an open surject
onto those of $\mathcal C$ (local liftings are patched using the
flasqueness of $\mathcal A$), so global sections are right exact on such
sequences and dimension shifting gives $H^q(\mathcal A)=0$ for $q\ge1$.
Put $I=G(\mathcal F)$ and $J=I/\mathcal F$; this is the displayed
sequence, with $H^q(I)=0$ for $q\ge1$. The long exact sequence
$0\to H^0(\mathcal F)\to I(Y)\xrightarrow{d_Y}J(Y)\to H^1(Y_{\Et},\mathcal F)\to H^1(Y_{\Et},I)=0$
identifies $H^1(Y_{\Et},\mathcal F)$ with $\operatorname{coker}(d_Y)$ and
$H^0$ with $\ker d_Y$. Only the acyclicity of $I$ enters: $J$ is not
acyclic in general, since $H^q(J)\cong H^{q+1}(\mathcal F)$ for
$q\ge1$ (nonzero for $\mathbf Z/\ell$ on $\mathbf P^1$ over an
algebraically closed field), and a short exact sequence with both $I$
and $J$ acyclic would force $H^{\ge2}(\mathcal F)=0$.
