+++
id = "sk-def-frobmod"
kind = "section"
title = "Frobenius modules and their trace series"
order = 2387
lean = ["LinearMap.traceSeries", "LinearMap.alternatingTraceSeries"]
+++
*Definition (sketch).*

A *Frobenius module* is a pair $(V,F)$ consisting of a
finite-dimensional $\Qlb$-vector space $V$ and a $\Qlb$-linear automorphism
$F:V\to V$. Its *trace series* and *determinant* are

$$
\operatorname{tr}_F(T)=\sum_{n\ge1}\Tr(F^{n}\mid V)\frac{T^{n}}{n},
\qquad
P_{(V,F)}(T)=\det(1-TF\mid V).
$$

For a finite graded family $(V_i,F_i)_{i\in I}$ ($I\subset\Z$ finite) the
*alternating trace series* is
$\operatorname{str}_F(T)=\sum_{n\ge1}\bigl(\sum_{i\in I}(-1)^{i} \Tr(F_i^{n}\mid V_i)\bigr)\frac{T^{n}}{n}$.
No semisimplicity of $F$ is assumed anywhere.
