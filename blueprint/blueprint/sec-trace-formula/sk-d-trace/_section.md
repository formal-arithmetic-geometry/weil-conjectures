+++
id = "sk-d-trace"
kind = "section"
title = "Ordinary categorical trace"
order = 2273
uses = ["sk-d-setup"]
lean = ["CategoryTheory.MonoidalCategory.trace"]
+++
*Definition (sketch).*

For $P\in\Perf(R)$, let
$P^\vee=R\operatorname{Hom}_R(P,R)$. Evaluation and coevaluation give its
duality in the symmetric monoidal category $(\Perf(R),\otimes_R^{\mathrm L},R)$.
For $v:P\to P$, define

$$
\tr_R(v\mid P)=
\bigl[R\xrightarrow{\mathrm{coev}}P\otimes P^\vee
\xrightarrow{v\otimes1}P\otimes P^\vee
\xrightarrow{\mathrm{sym}}P^\vee\otimes P
\xrightarrow{\mathrm{ev}}R\bigr].
$$

Uses: [sk-d-setup]
