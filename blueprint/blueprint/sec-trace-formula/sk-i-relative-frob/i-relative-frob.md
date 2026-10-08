+++
id = "i-relative-frob"
kind = "theorem"
title = "Relative Frobenius"
order = 2362
uses = ["d-relative-frob", "def-weil-scheme-morphism-properties"]
tags = ["latex:proposition"]
+++
In the setting of [d-relative-frob], for every $m\geq1$ the map
$r_m:X\to X'_m$ is finite and a universal homeomorphism
([def-weil-scheme-morphism-properties]).

## Proof

Put $Q=q^m$. By [d-relative-frob], $r_m$ is the base change along
$k_0\to k$ of the relative $Q$-power Frobenius
$F_{X_0/Y_0}:X_0\to X_0^{(Q)}$. Finite morphisms and universal
homeomorphisms are stable under base change, so it suffices to prove
that $F_{X_0/Y_0}$ is finite and a universal homeomorphism. Write
$\pi:X_0^{(Q)}\to X_0$ for the second projection, the base change of
$F_{Y_0}$ along $f_0$; then $\pi\circ F_{X_0/Y_0}=F_{X_0}$.

*Step 1: finiteness.* Since $\pi\circ F_{X_0/Y_0}=F_{X_0}$ is the
identity on underlying spaces, for affine opens
$\operatorname{Spec}R\subseteq Y_0$ and
$\operatorname{Spec}S\subseteq f_0^{-1}(\operatorname{Spec}R)$ the
inverse image under $F_{X_0/Y_0}$ of the affine open
$\operatorname{Spec}(R\otimes_{F,R}S)\subseteq X_0^{(Q)}$ is
$\operatorname{Spec}S$, and such opens cover $X_0^{(Q)}$. Finiteness is
local on the target, so it suffices that the ring map
$R\otimes_{F,R}S\to S$, $r'\otimes s\mapsto f_0^\#(r')s^Q$, of
[d-relative-frob] is finite. Choose generators $s_1,\ldots,s_n$ of the
finitely generated $R$-algebra $S$. Its image contains $f_0^\#(R)$ and
all $Q$-th powers. Every element of $S$ is an $f_0^\#(R)$-linear
combination of monomials $s^e=\prod_is_i^{e_i}$, and writing
$e_i=Qa_i+b_i$ with $0\leq b_i<Q$ gives $s^e=(s^a)^Q\,s^b$. Hence the
$Q^n$ monomials $s^b$ with $0\leq b_i<Q$ generate $S$ as a module over
the image, and the ring map is finite.

*Step 2: absolute Frobenius.* For an $\mathbf F_p$-scheme $T$, the
absolute $Q$-power Frobenius $F_T$ is the identity on the underlying
space, hence bijective; it is integral, since every local section $b$
is a root of $t^Q-b^Q$ whose coefficient $b^Q$ lies in the image; and
on residue fields it induces $\kappa\to\kappa$, $a\mapsto a^Q$, a
purely inseparable extension. Thus $F_T$ is radicial, that is,
universally injective, and being integral, universally injective and
surjective it is a universal homeomorphism
([Stacks, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)). In
particular $F_{Y_0}$ is one, and so is its base change $\pi$.

*Step 3: universal homeomorphism.* The morphism $F_{X_0/Y_0}$ is
integral by Step 1. It is surjective: for $x'\in X_0^{(Q)}$ choose $x$
with $F_{X_0}(x)=\pi(x')$ (Step 2); then
$\pi(F_{X_0/Y_0}(x))=\pi(x')$, and $\pi$ is injective, so
$F_{X_0/Y_0}(x)=x'$. It is universally injective: a morphism is
universally injective if and only if it is injective on $K$-valued
points for every field $K$, and on $K$-points
$\pi\circ F_{X_0/Y_0}=F_{X_0}$ is injective by Step 2, so
$F_{X_0/Y_0}$ is injective on $K$-points. By
[Stacks, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF) again,
$F_{X_0/Y_0}$ is a universal homeomorphism. With Step 1 and the
reduction at the beginning, $r_m$ is a finite universal homeomorphism.
