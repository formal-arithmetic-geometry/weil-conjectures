+++
id = "lem-sc-as-sequence"
kind = "lemma"
title = "The Artin–Schreier sequence"
order = 980
uses = ["def-sc-curves"]
+++
Let $C$ be a curve over a field $k$ of
characteristic $p>0$. The sequence of etale sheaves on
$C_{\Et}$

$$
0\longrightarrow\mathbf F_p\longrightarrow\mathbf G_a
\xrightarrow{\ \wp\ }\mathbf G_a\longrightarrow0,
\qquad \wp(x)=x^p-x,
$$

is exact.

## Proof

The kernel of $\wp$ is the constant sheaf $\mathbf F_p$: its
stalk at a geometric point $\bar x$ is
$\{a\in\mathcal O^{sh}_{C,\bar x}:a^p=a\}=\mathbf F_p$ (reduce
modulo the maximal ideal, whose residue field is $k$, and use the
Krull intersection theorem). For surjectivity: let $U\to C$ be
etale and $f\in\mathbf G_a(U)=\mathcal O_U(U)$. The scheme

$$
V:=\operatorname{Spec}\mathcal O_U[y]/(y^p-y-f)\to U
$$

is finite (free of rank $p$), flat (free), unramified (the
derivative of $y^p-y-f$ is $-1$, a unit), and surjective (the
fibre over every maximal ideal is a nonzero $k$-algebra), hence a
finite etale covering on which $\wp(y)=f$; therefore $\wp$ is
surjective as a morphism of etale sheaves.
