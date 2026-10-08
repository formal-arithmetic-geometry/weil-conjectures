+++
id = "lem-pur-divisor-class"
kind = "lemma"
title = "Kummer class of a divisor and its $c_1$"
order = 1945
uses = ["def-coefficient-twists-detailed", "def-pur-affine-line-datum", "def-pur-conventions", "def-pur-frame-class", "def-pur-support-cohomology", "def-weil-derived-cohomology-sheaves", "lem-pur-frame-independence", "lem-pur-kummer-additivity"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $T\to B$ be smooth of relative dimension $n$ and let
$D\hookrightarrow T$ be a closed subfamily, smooth over $B$, of pure
codimension one. The *Kummer class of the divisor $D$* is the
class $\operatorname{cl}(D)\in H^2_D(T,\Lambda(1))$ of
[def-pur-frame-class] of a frame of the ideal of $D$, well
defined by [lem-pur-frame-independence]. Moreover:

$$
\begin{array}{rcll}
\text{(a)}& \operatorname{cl}(D)|_{D\cap U}=\partial(\kappa(f))&
\text{for a local equation }f\text{ of }D\text{ on }U,&\\
\text{(b)}& \operatorname{cl}(D_1+D_2)=\operatorname{cl}(D_1)+\operatorname{cl}(D_2),&
\text{and forgetting support sends }\operatorname{cl}(D)\text{ to }c_1(\mathcal O_T(D)).&
\end{array}
$$

## Proof

Use the frame class of [def-pur-frame-class], independent of the local equation by [lem-pur-frame-independence], and the support boundary of [def-pur-support-cohomology] applied to the Kummer datum of [def-pur-affine-line-datum].
(a) is (def. frame class) $\operatorname{cl}(f)=\partial(\kappa(f))$.
For (b), the sum of two effective divisors $D_1,D_2$ has a frame
$(f_1,f_2)$ on an intersection of the two trivializing opens, and
$\kappa(f_1f_2)=\kappa(f_1)+\kappa(f_2)$ by
[lem-pur-kummer-additivity], so
$\operatorname{cl}(D_1)+\operatorname{cl}(D_2)$ is the class of the
frame $(f_1f_2)$. The forget-support statement is the standard
computation of the Kummer boundary of the group law of
$\operatorname{Pic}$: on a trivializing open the class
$\operatorname{cl}(D)$ is the boundary of the Kummer class of the
inverse image of the line bundle $\mathcal O_T(D)$'s unit section on
$T\setminus D$, hence its image in $H^2(T,\Lambda(1))$ is
$c_1(\mathcal O_T(D))$ of [lem-pur-kummer-additivity] (the
boundary maps in the two long exact sequences to $H^2(T,\Lambda(1))$,
and both are the image of the same class of $H^1(T,\mathbf G_m)$;
the statement is local and follows from the sheaf-theoretic
description of $c_1$ via the Kummer sequence).
