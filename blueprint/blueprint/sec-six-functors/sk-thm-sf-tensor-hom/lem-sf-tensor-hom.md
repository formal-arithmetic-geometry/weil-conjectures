+++
id = "lem-sf-tensor-hom"
kind = "lemma"
title = "Tensor–Hom form of the exchange"
order = 2167
uses = ["def-sf-datum", "def-sf-pf", "def-trf-admissibility", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-inverse-image", "fix-lem-tensor-adjunction", "fix-prop-adjunctions"]
+++
In the setting of [def-sf-datum], let $f:X\to Y$ be a separated
finite-type morphism, with $Rf^!$ the constructible exceptional inverse image
of [def-weil-exceptional-inverse-image] (no admissibility datum is assumed;
every such $f$ is exceptionally admissible in the sense of
[def-trf-admissibility]), $M\in D^b_{ctf}(X,\Lambda)$ and
$N\in D^b_{ctf}(Y,\Lambda)$. Then there is a canonical isomorphism

$$
Rf_*R\mathcal H om_X(M,f^!N)\xrightarrow{\ \sim\ }
R\mathcal H om_Y(Rf_!M,N),
$$

natural in $M$ and $N$ and compatible with finite reduction, scalar
extension, and shifts. ([fix-lem-tensor-adjunction]; the
proof is the one given there, recalled here because the whole formal core
rests on it.)

## Proof

The adjunctions and the projection transformation used throughout are
those recorded in [fix-prop-adjunctions] and
[fix-lem-tensor-adjunction], in the form fixed by [def-sf-pf].
Step 1: for every $L\in D^b_{ctf}(Y,\Lambda)$ the adjunctions of axiom
(A1) and the tensor–internal-Hom adjunction of
[def-weil-derived-pullback-tensor-hom] give the chain

$$
\begin{aligned}
\operatorname{Hom}_Y\bigl(L,R\mathcal H om_Y(Rf_!M,N)\bigr)
&\cong\operatorname{Hom}_Y(Rf_!M\otimes^L_\Lambda L,N)\\
&\cong\operatorname{Hom}_Y\bigl(Rf_!(M\otimes^L_\Lambda Lf^*L),N\bigr)\\
&\cong\operatorname{Hom}_X\bigl(M\otimes^L_\Lambda Lf^*L,f^!N\bigr)\\
&\cong\operatorname{Hom}_X\bigl(Lf^*L,R\mathcal H om_X(M,f^!N)\bigr)\\
&\cong\operatorname{Hom}_Y\bigl(L,Rf_*R\mathcal H om_X(M,f^!N)\bigr),
\end{aligned}
$$

the second isomorphism being the *inverse* of the projection formula
(axiom (A3), [def-sf-pf]), the third the adjunction
$Rf_!\dashv Rf^!$, and the first, fourth and fifth the tensor–internal-Hom
adjunction together with $Lf^*\dashv Rf_*$. Step 2: the chain is natural
in $L$, so the two objects represent the same functor on
$D^b_{ctf}(Y,\Lambda)$; the Yoneda lemma applied to degree-zero morphisms
of that triangulated category gives the canonical isomorphism, whose
naturality and compatibilities are those of the ingredients.
