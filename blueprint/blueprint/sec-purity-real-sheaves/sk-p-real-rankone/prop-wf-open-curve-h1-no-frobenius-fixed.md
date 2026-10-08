+++
id = "prop-wf-open-curve-h1-no-frobenius-fixed"
kind = "theorem"
title = "No Frobenius-fixed compatible class on an open normal curve"
order = 2625
tags = ["latex:proposition"]
uses = ["def-tw-frobenius-action", "def-weil-pbc-scheme-conventions", "lem-wf-curve-normal-smooth-compactification", "lem-wf-open-curve-residue-sequence", "lem-wf-proper-curve-compatible-h1-no-fixed"]
+++
Let $U_0/\mathbf F_q$ be normal, geometrically connected,
separated and of finite type,
pure of dimension one, and put
$U=U_0\times_{\mathbf F_q}\overline{\mathbf F}_q$. If
$\ell\nmid q$, then for the
geometric Frobenius

$$
\left(\varprojlim_nH^1_{\mathrm{\acute et}}
(U,\mathbf Z/\ell^n\mathbf Z)\right)^{\Phi_q=1}=0.
\tag{5.4}
$$

The scheme and Frobenius conventions are those of
[def-weil-pbc-scheme-conventions], [def-tw-frobenius-action].

## Proof

Choose the smooth projective geometrically connected compactification
$j_0:U_0\hookrightarrow C_0$ and finite reduced boundary $D_0$ from
[lem-wf-curve-normal-smooth-compactification]. Let
$z=(z_n)_n$ be fixed by $\Phi_q$ in the inverse limit in (5.4).
Choose $m$ as in [lem-wf-open-curve-residue-sequence] and put
$Q=q^m$. The residues
$r_n=\operatorname{res}_n(z_n)$ form a compatible element
$r=(r_n)_n$ of the inverse-limit boundary module and are fixed by
$\Phi_Q$. The last assertion of the residue lemma gives $r=0$, hence
$r_n=0$ for every $n$.

Exactness of (5.1) gives a unique $x_n\in H^1(C,A_n)$ with
$j^*x_n=z_n$. Uniqueness shows that the $x_n$ are compatible under
reduction. Injectivity of $j^*$ and Frobenius equivariance show that
$\Phi_Qx_n=x_n$. Thus $x=(x_n)_n$ is a fixed element of
$\varprojlim_nH^1(C,A_n)$. Put
$C_{0,Q}:=C_0\times_{\mathbf F_q}\mathbf F_Q$. Its geometric fiber is
the same $C$, and its geometric Frobenius is $\Phi_q^m=\Phi_Q$.
Apply [lem-wf-proper-curve-compatible-h1-no-fixed] to
$C_{0,Q}/\mathbf F_Q$; it gives $x=0$, and then
$z_n=j^*x_n=0$ for every $n$.
