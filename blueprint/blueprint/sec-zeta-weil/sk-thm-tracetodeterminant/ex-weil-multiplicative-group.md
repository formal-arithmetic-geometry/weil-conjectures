+++
id = "ex-weil-multiplicative-group"
kind = "remark"
title = "Multiplicative-group compact-support normalization"
order = 2883
tags = ["latex:example"]
uses = ["def-weil-finite-field-fiber", "def-weil-frobenius-coefficient-twists", "def-weil-frobenius-detailed", "def-weil-ordinary-compact-cohomology"]
+++
Fix the finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, and choose a prime $\ell\neq p$. Write
$\Ql=\mathbf Q_\ell$. Put
$Y_0=\mathbf G_{m,k_0}$, and set $Y=Y_0\times_{k_0}k$. One has
$H_c^1(Y,\Ql)\cong\Ql$ and $H_c^2(Y,\Ql)\cong\Ql(-1)$. The
geometric Frobenius
has eigenvalues $1$ and $q$, respectively, under the
compact-support cohomology
and Tate-twist
conventions.
Thus, for every integer $n\geq1$,
$\#Y_0(\mathbf F_{q^n})=q^n-1$ and
$Z(Y_0,T)=(1-T)/(1-qT)$.
