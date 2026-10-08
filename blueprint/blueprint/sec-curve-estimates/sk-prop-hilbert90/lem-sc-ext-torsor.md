+++
id = "lem-sc-ext-torsor"
kind = "lemma"
title = "Extensions and torsors"
order = 879
+++
Let $X$ be a scheme and $G$ an abelian sheaf on $X_{\Et}$.
There is a canonical bijection

$$
\operatorname{Ext}^1_{\mathrm{Ab}(X_{\Et})}(\mathbf Z_X,G)
\cong\{\text{isomorphism classes of }G\text{-torsors}\}.
$$

## Proof

Given an extension
$0\to G\xrightarrow{\iota}E\xrightarrow{\pi}\mathbf Z_X\to0$, the
preimage $T:=\pi^{-1}(1)\subseteq E$ of the section $1$ is a
$G$-torsor: the $G$-action is free and transitive, the stalks of
$T$ are nonempty because $\pi$ is surjective as a morphism of
sheaves, and a section $t\in T(U)$ trivializes
$T|_U\xrightarrow{\sim}G|_U$ via $g\mapsto\iota(g)+t$.

Conversely, given a $G$-torsor $T$, define an abelian sheaf
$E$ on $X_{\Et}$ by

$$
E:=\coprod_{n\in\mathbf Z}T^{\otimes n},
$$

where for $n\geq1$, $T^{\otimes n}$ is the $n$-fold contracted
product $(T\times\cdots\times T)/G$ with the antidiagonal action
$g\cdot(t_1,\dots,t_n)=(t_1+g,t_2-g,t_3+g,\dots)$,
$T^{\otimes0}:=G$, and $T^{\otimes(-n)}$ is the $n$-fold
contracted product of the inverse torsor $T^{-1}$ (the set $T$
with $G$ acting through negation). The group law on $E$ is the
concatenation

$$
T^{\otimes m}\times T^{\otimes n}\longrightarrow T^{\otimes(m+n)},
$$

$([t_1,\dots,t_m],[s_1,\dots,s_n])\mapsto[t_1,\dots,t_m,s_1,\dots,s_n]$;
this makes $E$ an abelian sheaf (associativity is the associativity
of contracted products, and the inverse is given by
$T^{\otimes n}\cong(T^{-1})^{\otimes n}$ componentwise). The map
$\pi:E\to\mathbf Z_X$ sending $T^{\otimes n}$ to $n$ is a
homomorphism, surjective because its stalks are surjective (each
$T^{\otimes n}$ is a torsor, hence has nonempty stalks), and its
kernel is $T^{\otimes0}=G$; thus
$0\to G\to E\xrightarrow{\pi}\mathbf Z_X\to0$ is exact. The two
constructions are mutually inverse: for the extension built from
$T$, the preimage of $1$ is $T^{\otimes1}=T$; and for the
torsor $T:=\pi^{-1}(1)$ of an extension $E$, the addition of
$E$ induces isomorphisms
$\pi^{-1}(n)\xrightarrow{\sim}T^{\otimes n}$,
$(e_1,\dots,e_n)\mapsto e_1+\cdots+e_n$, which identify $E$ with
$\coprod_nT^{\otimes n}$.
