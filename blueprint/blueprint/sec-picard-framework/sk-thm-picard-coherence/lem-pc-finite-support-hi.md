+++
id = "lem-pc-finite-support-hi"
kind = "lemma"
title = "Finite support of higher direct images"
order = 642
uses = ["def-pc-morphism-conventions", "def-pc-scheme", "lem-pc-affine-vanishing", "lem-pc-cech-computes"]
+++
Let $f:X\to S$ be a quasi-compact, quasi-separated morphism of schemes.
For every quasi-coherent $\mathcal{O}_X$-module $\mathcal{F}$:

1. the $R^if_*\mathcal{F}$ are quasi-coherent;
1. if $S$ is quasi-compact, there is an integer $n=n(X,S,f)$ such
that $R^pf_*\mathcal{F}=0$ for all $p\ge n$ and all quasi-coherent $\mathcal{F}$; the
same integer works for every base change
$S'\to S$ (i.e. $R^p(f')_*\mathcal{F}'=0$ for $p\ge n$ and quasi-coherent
$\mathcal{F}'$ on $X'=S'\times_SX$).

## Proof

It suffices to prove the statements on affine open subschemes
$V=\operatorname{Spec}(A)$ of $S$ (the sheaf $R^if_*\mathcal{F}$ is determined by its
sections on affines, and $(R^if_*\mathcal{F})|_V=R^i(f|_V)_*\mathcal{F}|$): after
replacing $S$ by $V$ and $X$ by $f^{-1}(V)$ we have an affine $S$,
and $X$ is quasi-compact and quasi-separated. Choose a finite affine
open covering $X=U_1\cup\dots\cup U_t$ (quasi-compactness) with all
intersections affine (quasi-separatedness: the intersection of two
affine open subschemes of a quasi-separated scheme is affine; or
refine). We prove by induction on $t$ the assertion
$P(t)$: $H^p(X,\mathcal{F})=0$ for $p\ge t$ and $H^p(X,\mathcal{F})=\check H^p(\mathcal U,\mathcal{F})$
for all $p$, for every quasi-coherent $\mathcal{F}$. For $t=1$, $X$ affine and
$P(1)$ is [lem-pc-affine-vanishing]. For $t>1$ write
$U=U_1$, $V=U_2\cup\cdots\cup U_t$ ($V$ is quasi-compact, covered by
$t-1$ affine opens with affine intersections) and consider the short
exact sequence of sheaves on $X$

$$
0\to\mathcal{F}\longrightarrow j_{U,*}\mathcal{F}|_U\oplus j_{V,*}\mathcal{F}|_V
\longrightarrow j_{U\cap V,*}\mathcal{F}|_{U\cap V}\to0
$$

(exactness is immediate on stalks: at $x$, the sequence is
$0\to\mathcal{F}_x\to\mathcal{F}_x\oplus\mathcal{F}_x\to\mathcal{F}_x\to0$ for $x\in U\cap V$, and
$0\to\mathcal{F}_x\to\mathcal{F}_x\to0\to0$ otherwise, with the maps the diagonal and
the difference). Its long exact cohomology sequence, together with
$H^p(U,\cdot)=H^p(V,\cdot)=0$ for $p\ge t-1$ and the identifications
$H^p(U,\mathcal{F})=\check H^p(U,\mathcal{F})$ etc. (the induction hypothesis applied
to $U$ ($t=1$) and to $V$ ($t-1$ opens) and the standard equality for
a two-open cover), gives $H^p(X,\mathcal{F})=0$ for $p\ge t$ and the Cech
identification for lower $p$ (the classical devissage of Cohomology of
Schemes, Lemma 30.4.5, Tag [01XJ](https://stacks.math.columbia.edu/tag/01XJ),
which also uses [lem-pc-cech-computes] for the Cech comparison).
This proves (1) and the first statement of (2) (the integer $n=t$).
The base-change uniformity: the same $t$ bounds the coverings obtained
by base change $S'\to S$: the $U_i$'s pull back to affine opens of
$X'$ with affine intersections covering $X'$ (base change of affine
along $S'\to S$ is affine; $\mathcal{F}$ replaced by an arbitrary
quasi-coherent $\mathcal{F}'$), so the same induction proves $R^p(f')_*\mathcal{F}'=0$
for $p\ge t$. This proves (2).
