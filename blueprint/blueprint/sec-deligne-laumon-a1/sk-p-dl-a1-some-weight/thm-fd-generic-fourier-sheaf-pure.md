+++
id = "thm-fd-generic-fourier-sheaf-pure"
kind = "theorem"
tags = ["latex:proposition"]
title = "The generic Fourier sheaf is pure of some weight"
order = 2776
uses = ["cor-wf-unramified-boundary-purity", "def-a1-constituent-nonexceptional", "def-fd-transform", "def-weil-punctual-weights", "def-wf-determinantal-weight", "def-wf-iota-real", "def-wf-middle-extension", "fin2-lem-lisse-dense-open", "lem-a1-constituent-nonexceptional-comparison", "lem-fd-constituent-nonexceptional-concentration", "lem-fd-realified-kernel-real", "lem-fd-realness-pushforward", "prop-a1-fourier-middle-extension", "prop-fd-zero-extension-comparison", "rem-dl-a1-conventions", "thm-rp-real-lisse-purity-affine"]
lean = ["AlgebraicGeometry.exists_isPunctuallyPureOfWeight_of_isFourierPartner"]
+++
In the conventions of [rem-dl-a1-conventions], let
$j:U_0\hookrightarrow A_0=\mathbf A^1_{k_0}$ be a dense open immersion
and let $\mathcal M$ be a nonzero irreducible lisse Weil sheaf on $U_0$
which is constituent-nonexceptional in the sense of
[def-a1-constituent-nonexceptional] and punctually $\iota$-pure of
weight $w$. Let $j':U'_0\hookrightarrow A'_0$ and the nonzero irreducible
lisse Weil sheaf $\mathcal M'$ on $U'_0$ be those of
[prop-a1-fourier-middle-extension], so that

$$
\operatorname{FT}_\psi\bigl((j_*\mathcal M)[1]\bigr)\cong(j'_*\mathcal M')[1].
$$

Then $\mathcal M'$ is punctually $\iota$-pure, on all of $U'_0$, of some
real weight $v$ (in the sense of [def-weil-punctual-weights]).

## Proof

*Step 1: the real envelope after zero extension.* Put
$b=\iota^{-1}(q^w)$, $\mathcal M^\dagger=\mathcal M^\vee\otimes\mathcal B_b$,
and let $\mathcal K$ be the realified kernel on the Fourier square formed
from $j_!\mathcal M$ and $j_!\mathcal M^\dagger$ as in
[lem-fd-realified-kernel-real]. By the general form of
[lem-fd-realified-kernel-real], which needs only the purity of
$\mathcal M$, the constructible Weil sheaf $\mathcal K$ is $\iota$-real.
By [lem-fd-constituent-nonexceptional-concentration](3),
$R^\nu p_{2,!}\mathcal K=0$ for $\nu\neq1$, and the sheaf

$$
\mathcal G:=\operatorname{FT}_\psi(j_!\mathcal M)
$$

(concentrated in degree $0$) is a direct summand of
$\mathcal H:=R^1p_{2,!}\mathcal K$. By [lem-fd-realness-pushforward],
applied to $\mathcal K$ and this vanishing, $\mathcal H$ is an
$\iota$-real constructible Weil sheaf on the dual line $A'_0$. Working
with $j_!\mathcal M$ rather than $j_*\mathcal M$ is what makes the
reality available: at a missing point both summands of $\mathcal K$ have
zero stalk, while the boundary stalks of $j_*\mathcal M$ and
$j_*\mathcal M^\dagger$ need not have conjugate spectra.

*Step 2: $\mathcal G$ surjects onto the middle extension.* By the
zero-extension comparison [prop-fd-zero-extension-comparison], whose
hypotheses are exactly those of the present statement,
$\operatorname{FT}_\psi(j_!\mathcal M[1])\cong\mathcal G[1]$ and there is
a short exact sequence of Weil sheaves
$0\to\mathcal B'\to\mathcal G\to j'_*\mathcal M'\to0$ on the dual line,
with $j'_*\mathcal M'$ the middle extension of
[def-wf-middle-extension]. In particular
$\mathcal G\to j'_*\mathcal M'$ is an epimorphism of Weil sheaves.

*Step 3: purity on a dense open.* By [fin2-lem-lisse-dense-open],
applied to $\mathcal H$ and to $\mathcal G$ and intersected with
$U'_0$, there is a dense open $V'_0\subset U'_0$ on which $\mathcal H$
and $\mathcal G$ are lisse. Restriction to $V'_0$ is exact and additive,
and $(j'_*\mathcal M')|_{V'_0}=\mathcal M'|_{V'_0}$. Composing the
projection $\mathcal H\to\mathcal G$ onto the direct summand with the
epimorphism of Step 2 gives an epimorphism of lisse Weil sheaves

$$
\mathcal H|_{V'_0}\twoheadrightarrow\mathcal M'|_{V'_0}.
$$

The restriction $\mathcal M'|_{V'_0}$ is nonzero and irreducible: the
Weil group of the dense open $V'_0$ of the normal connected curve
$U'_0$ surjects onto that of $U'_0$ (the corresponding surjectivity of
étale fundamental groups for a dense open of a normal connected scheme,
SGA 1, Exp. V, 8.2), so the invariant subspaces are the same. Refining
the kernel of this epimorphism to a composition series of
$\mathcal H|_{V'_0}$ shows that $\mathcal M'|_{V'_0}$ is an irreducible
constituent of $\mathcal H|_{V'_0}$, which is lisse and $\iota$-real
([def-wf-iota-real]; reality is a pointwise condition and passes to
the open). As $V'_0$ is a dense open of the affine line, it is a smooth
geometrically connected affine curve, and
[thm-rp-real-lisse-purity-affine] shows that $\mathcal M'|_{V'_0}$ is
punctually $\iota$-pure of the real weight
$v:=\dw_\iota(\mathcal M'|_{V'_0})$, its determinantal weight of
[def-wf-determinantal-weight].

*Step 4: purity on all of $U'_0$.* The sheaf $\mathcal M'$ is lisse on
the smooth geometrically connected curve $U'_0$ and its restriction to
the dense open $V'_0$ is punctually $\iota$-pure of weight $v$. At a
point $x\in U'_0\setminus V'_0$ the inertia acts trivially, $\mathcal M'$
being lisse there, and the ordinary direct image from $V'_0$ recovers the
stalk of $\mathcal M'$ (the translation step of
[lem-a1-constituent-nonexceptional-comparison]). The consequence
clause of [cor-wf-unramified-boundary-purity] therefore gives that
$\mathcal M'$ is punctually $\iota$-pure of weight $v$ on all of
$U'_0$.
