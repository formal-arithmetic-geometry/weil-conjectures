+++
id = "def-weil-constructible-intervals"
kind = "definition"
title = "Constructible cohomological intervals"
order = 1466
uses = ["def-weil-derived-cohomology-sheaves", "def-weil-finite-torsion-constructibility"]
+++
Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and a scheme $Y$ on which $\ell$ is invertible, as well as
integers $a,b\in\mathbf Z$ with $a\leq b$. Put $A=A_{E,n}$, and use the
derived cohomology sheaves [def-weil-derived-cohomology-sheaves] $\mathcal
H^r$. Define

$$
D_c^{[a,b]}(Y,A)=
\{K\in D^b_c(Y,A):
\mathcal H^r(K)=0\text{ for every }
r\in\mathbf Z\setminus[a,b]\}.
$$

Here $D^b_c(Y,A)$ is the bounded category with the finite-torsion
constructibility condition [def-weil-finite-torsion-constructibility].
