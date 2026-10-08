+++
id = "lem-kun-descent-limit-open"
kind = "lemma"
title = "Descent of a quasi-compact open in an affine limit"
order = 1659
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $X=\varprojlim_iX_i$ be a directed inverse limit of
affine schemes
$X_i=\Spec(A_i)$ with affine transition morphisms, so that $X$ is
affine with coordinate ring $A=\varinjlim_iA_i$, and let $U\subseteq X$
be a quasi-compact open subscheme. Then there are $i$ and a
quasi-compact open $U_i\subseteq X_i$ with
$U=p_i^{-1}(U_i)=U_i\times_{X_i}X$.
(*Source:* the affine case of the descent of a quasi-compact open
along an affine limit, Stacks Project, Limits of Schemes,
[Lemma 32.10.1, Tag
`01ZM`](https://stacks.math.columbia.edu/tag/01ZM); the general case of that tag, for arbitrary quasi-compact
quasi-separated $X_i$, is not needed in this chapter.)

## Proof

An inverse limit of affine schemes with affine transition morphisms is
affine, with coordinate ring the filtered colimit of the coordinate rings,
and the transition maps of the limit are the maps
$\Spec(A)\to\Spec(A_i)$ induced by the structural maps
$A_i\to A$; moreover
$p_i^{-1}(D(g))=D(p_i^\sharp(g))$ for $g\in A_i$.

A quasi-compact open subscheme of the affine scheme $X=\Spec(A)$ is the
complement of the zero set of a finitely generated ideal: there are
$f_1,\dots,f_n\in A$ with

$$
U=D(f_1)\cup\cdots\cup D(f_n)=D(f_1,\dots,f_n).
$$

Each $f_j$ is the image of an element of some $A_i$, and because the
index system is directed and filtered, the finitely many elements
$f_1,\dots,f_n$ all come from a common index: there are $i$ and
$g_1,\dots,g_n\in A_i$ with $p_i^\sharp(g_j)=f_j$ for all $j$. Put
$U_i=D(g_1,\dots,g_n)\subseteq X_i$, a quasi-compact open subscheme.
Then

$$
p_i^{-1}(U_i)=D(p_i^\sharp(g_1),\dots,p_i^\sharp(g_n))
=D(f_1,\dots,f_n)=U,
$$

which is the assertion.
