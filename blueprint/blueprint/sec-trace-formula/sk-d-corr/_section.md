+++
id = "sk-d-corr"
kind = "section"
title = "Correspondences and supported classes"
order = 2275
uses = ["sk-d-setup", "sk-d-six", "sk-thm-sf-comp-composition"]
lean = ["AlgebraicGeometry.ProEtale.Correspondence"]
+++
*Definition (sketch).*

Let $X,Y,C,D$ be geometric schemes, with
$K\in D^b_{ctf}(X,A)$ and $L\in D^b_{ctf}(Y,A)$.
A correspondence from $(X,K)$ to $(Y,L)$ consists of
$c=(c_1,c_2):C\to Y\times X$ and
$u:c_2^*K\to c_1^!L$, using the geometric operations.
The ordinary-pullback leg is $c_2$. For an opposite correspondence
$d=(d_1,d_2):D\to X\times Y$, $v:d_2^*L\to d_1^!K$, put

$$
Z=Y\times X,\quad \bar d=\tau d,\quad E(C,D)=C\times_ZD.
$$

Here $\tau$ exchanges factors. For an endocorrespondence,
$F=\Fix(c)=C\times_{X\times X,\,c,\,\Delta_X}X$.
For $i:T\to Z$, a class supported on $i$ means an element of
$H_T^0(Z,P)=\operatorname{Hom}(Ri_!A_T,P)$.
Tensor–Hom adjunction, the projection formula, and exceptional adjunction
define $[u]$ as the inverse image of $u$ under

$$
\operatorname{Hom}\bigl(Rc_!A_C,\RHom_A(p_2^*K,p_1^!L)\bigr)
\simeq\operatorname{Hom}(c_2^*K,c_1^!L).
$$

All supports and structure maps remain specified data.

Uses: [sk-d-setup], [sk-d-six]
