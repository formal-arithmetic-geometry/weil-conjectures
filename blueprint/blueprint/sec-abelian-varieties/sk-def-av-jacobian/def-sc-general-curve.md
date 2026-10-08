+++
id = "def-sc-general-curve"
kind = "definition"
title = "Curves over an arbitrary field"
order = 463
uses = ["def-pc-base-change", "def-pc-geometrically-irreducible", "def-pc-smooth-projective-curve", "def-sc-curves", "def-sc-genus", "def-sc-pic0"]
+++
Let $k$ be a field. A *geometrically integral smooth projective curve
over $k$* is a scheme $C$ over $k$ which is
smooth and projective over $k$
and geometrically integral over
$k$. Its *genus* is

$$
g(C):=\dim_kH^1(C,\mathcal O_C),
$$

finite because coherent cohomology of a proper scheme over a field is
finite-dimensional, and invariant under base change,
$g(C_{k'})=g(C)$ for every field extension $k'/k$, by flat base change
along the base change of [def-pc-base-change]. For an algebraically
closed extension $k'/k$ the base change $C_{k'}$ is a
proper smooth connected curve in the sense of the
algebraically closed conventions of the smooth-curve chapter, and
$g(C)=g(C_{k'})$ with the genus of [def-sc-genus]; in particular the
degree and $\operatorname{Pic}^0$ conventions of [def-sc-pic0] apply to
$C_{k'}$. The statements of the present chapter that are formulated over an
arbitrary field use this definition; the algebraically closed statements use
[def-sc-curves].
