+++
id = "def-pur-frame-class"
kind = "definition"
title = "Class of a frame"
order = 1942
uses = ["def-coefficient-twists-detailed", "def-pur-affine-line-datum", "def-pur-conventions", "def-pur-supported-cup", "def-weil-derived-cohomology-sheaves", "thm-pur-with-support-exactness"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$A=A_{E,n}$, let $V\to B$ be smooth of relative dimension $n$ and
let $Z\hookrightarrow V$ be a closed subfamily of pure codimension $c$
with $Z\to B$ smooth. A *frame at $Z$* is an etale open
$U\to V$ together with functions $f_1,\dots,f_c\in\Gamma(U,\mathcal O)$
generating the ideal of $Z\cap U$. Put $D_j=V(f_j)$; the function
$f_j$ is a unit on $U\setminus D_j$. Use the boundary for this
individual closed–open pair from [thm-pur-with-support-exactness]
to define $\alpha_j=\partial_j\kappa(f_j)\in H^2_{D_j}(U,\Lambda(1))$.
The *class of the frame* is their
supported cup product

$$
\operatorname{cl}(f)
\;=\;\alpha_1\cup\cdots\cup\alpha_c
\;\in\;H^{2c}_{Z\cap U}\bigl(U,\Lambda(c)\bigr),
$$

where the Kummer classes are those of
[def-pur-affine-line-datum]. Each factor has degree two and
twist one; their supports intersect in $Z\cap U$, giving degree
$2c$ and twist $c$.
