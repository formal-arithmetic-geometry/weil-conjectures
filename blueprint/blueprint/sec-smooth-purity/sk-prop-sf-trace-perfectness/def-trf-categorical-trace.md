+++
id = "def-trf-categorical-trace"
kind = "definition"
title = "Perfect complex and its categorical trace"
order = 1826
uses = ["def-trf-coefficient-conventions", "def-weil-derived-tensor", "def-weil-finite-coefficient-point", "def-weil-finite-field-fiber"]
+++
Fix the global finite-field datum
and the coefficient
conventions, with $A=A_{E,n}$, and define
$D^b_{\mathrm{fin}}(A)$ to be the category of *perfect*
$A$-complexes, realized explicitly as the category of bounded
complexes of finitely generated projective $A$-modules, (The
perfect form is the one needed here: only perfect complexes are
dualizable with respect to the derived tensor, so only for them does
the coevaluation of the display below exist.)
For $P\in D^b_{\mathrm{fin}}(A)$ put
$P^\vee=R\operatorname{Hom}_A(P,A)$. The coevaluation and evaluation
are

$$
\operatorname{coev}_P:A\longrightarrow P\otimes_A^LP^\vee,\qquad
\operatorname{ev}_P:P^\vee\otimes_A^LP\longrightarrow A,
$$

the triangle identities for which are
[lem-trf-chain-supertrace]; here $\otimes^L_A$ is the
derived tensor over $A$. For an
endomorphism $v:P\to P$, the *categorical trace* is

$$
\operatorname{tr}_A(v\mid P):=
\operatorname{ev}_P\circ\operatorname{sym}\circ
\bigl(v\otimes_A^L1\bigr)\circ\operatorname{coev}_P
\in\operatorname{End}_{D(A)}(A)\cong A.
$$

The identification $\operatorname{End}_{D(A)}(A)\cong A$ is the
classical one (a bounded complex concentrated in degree $0$ with
zero differentials: the quasi-isomorphism class of an endomorphism of
$A$ is its degree-$0$ scalar).

*Recorded in advance* from chapter *The trace formula* of the source.
