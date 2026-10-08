+++
id = "ex-weil-affine-line"
kind = "remark"
title = "Affine-line compact-support normalization"
order = 2882
tags = ["latex:example"]
uses = ["def-weil-finite-field-fiber", "def-weil-frobenius-coefficient-twists", "def-weil-frobenius-detailed", "def-weil-ordinary-compact-cohomology"]
+++
Fix the finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, and choose a prime $\ell\neq p$. Write
$\Ql=\mathbf Q_\ell$. Put
$Y_0=\mathbf A^1_{k_0}$, and set $Y=Y_0\times_{k_0}k$. The
compact-support cohomology
construction gives
$H_c^2(Y,\Ql)\cong\Ql(-1)$ and no other compactly supported cohomology.
The Tate-twist convention
makes geometric Frobenius act by $q$, so, for
every integer $n\geq1$, the trace expression is
$\#Y_0(\mathbf F_{q^n})=q^n$ and
$Z(Y_0,T)=(1-qT)^{-1}$.
