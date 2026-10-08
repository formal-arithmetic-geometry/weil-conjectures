+++
id = "lem-pur-finite-kummer-level"
kind = "lemma"
title = "Finite Kummer level of the Tate twist"
order = 1890
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-derived-tensor", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
Fix the finite-field datum and $A=A_{E,n}$ of
[def-pur-conventions]; write $e=e(E/\Ql)$ for the ramification
index of $E/\Ql$ and assume that $e\mid n$. With $v_\ell$ normalized
by $v_\ell(\ell)=1$ (so that $v_\ell(\varpi_E)=1/e$), put

$$
N=n\cdot v_\ell(\varpi_E)\in\mathbf Z_{\geq1},
$$

the smallest exponent with $\ell^N\cdot A=0$; here $N=n/e$, and
$\varpi_E^n\mathcal O_E=\ell^N\mathcal O_E$, so that
$A=\mathcal O_E/\varpi_E^n\cong\mathcal O_E/\ell^N\mathcal O_E\cong (\mathbf Z/\ell^N\mathbf Z)^{ef}$
with $e=e(E/\Ql)$ the ramification index and $f=[\mathcal O_E/\varpi_E:\mathbf F_\ell]$ the residue degree,
is free of finite rank as a $\mathbf Z/\ell^N\mathbf Z$-module. Then there is a canonical isomorphism
of finite-torsion module sheaves on the small pro-etale site of any scheme
$T$ on which $\ell$ is invertible,

$$
A(1)_T\xrightarrow{\ \sim\ }\mu_{\ell^N,T}\otimes_{\mathbf Z/\ell^N}A,
$$

where $A(1)_T$ is the finite-level twist of
[def-coefficient-twists-detailed], $\mu_{\ell^N,T}$ is the etale sheaf of
$\ell^N$-th roots of unity, and $\otimes$ is over
$\mathbf Z/\ell^N\mathbf Z$. The isomorphism is compatible with the
derived tensor product and with base
change.

## Proof

Write the Tate object $\Zl(1)_T=\varprojlim_r\mu_{\ell^r,T}$ of
[def-coefficient-twists-detailed] as the projective limit of the surjective
transition maps, so that $\Zl(1)_T$ is a locally free $\Zl$-module of
rank one with $\Zl(1)_T/\ell^N\Zl(1)_T=\mu_{\ell^N,T}$, and
$A(1)_T=\Zl(1)_T\otimes_{\Zl}A$. In the exact sequence

$$
0\longrightarrow\ell^N\Zl(1)_T\longrightarrow\Zl(1)_T
\longrightarrow\mu_{\ell^N,T}\longrightarrow0
$$

the multiplication map $\Zl(1)_T\otimes_{\Zl}A\to \ell^N\Zl(1)_T\otimes_{\Zl}A$, $x\mapsto\ell^Nx$, is an isomorphism
(the module $\Zl(1)_T$ is a locally free rank-one line), and the
composite $\Zl(1)_T\otimes A\cong\ell^N\Zl(1)_T\otimes A\to \Zl(1)_T\otimes A$ is multiplication by $\ell^N$, which is zero since
$\ell^N$ kills $A$. Hence the induced map
$A(1)_T\to\mu_{\ell^N,T}\otimes_{\mathbf Z/\ell^N}A$ is an isomorphism.
The compatibility with the derived tensor product and with base change
is the naturality of the displayed projection and of the tensor
product.
