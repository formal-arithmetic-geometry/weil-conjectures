+++
id = "pqf-lem-limit-immersion-descends"
kind = "lemma"
title = "Closed immersions spread out from a filtered limit"
order = 196
uses = ["def-weil-pbc-scheme-conventions", "pqf-lem-affine-local-target"]
+++
Let $S$ be a scheme, let $X=\varprojlim_{i\in I}X_i$ be a filtered
limit of $S$-schemes with affine transition morphisms and
quasi-compact $X_i$, and let $Y\to X$ be a morphism of $S$-schemes
which is a closed immersion, with $Y$ locally of finite type over
$S$. Then the composite $Y\to X\to X_i$ is a closed immersion for
all sufficiently large $i$.
(*Stacks Project, Limits of Schemes, Lemma 32.4.16 (1)*,
[Tag 081B](https://stacks.math.columbia.edu/tag/081B).)

## Proof

Choose an index $0\in I$ and a finite affine open covering
$X_0=U_{0,1}\cup\dots\cup U_{0,m}$ such that each $U_{0,j}$ maps
into an affine open $W_j\subset S$: cover each point of the
quasi-compact $X_0$ by an affine open lying over an affine open of
$S$, possible because affine opens form a basis of both spaces, and
pass to a finite subcovering. For $i\ge0$ let $U_{i,j}\subset X_i$
be the preimage of $U_{0,j}$, and let $U_j\subset X$ and
$V_j\subset Y$ be the corresponding preimages; the opens $U_{i,j}$,
$j=1,\dots,m$, cover $X_i$. Each $U_{i,j}$ is affine, being the
base change $U_{0,j}\times_{X_0}X_i$ of the affine $U_{0,j}$ along
the affine morphism $X_i\to X_0$, and $U_j=\varprojlim_iU_{i,j}$ is
affine, the filtered limit of affine schemes with affine transition
morphisms being the spectrum of the filtered colimit of the coordinate
rings. Write $A_i=\mathcal O(U_{i,j})$, so that
$A=\mathcal O(U_j)=\varinjlim_iA_i$.

Since $Y\to X$ is a closed immersion, $V_j=Y\times_XU_j$ is a closed
subscheme of the affine $U_j$, so $V_j=\operatorname{Spec}B_j$ with
$B_j=A/\mathfrak a_j$. The restriction $V_j\to W_j$ of $Y\to S$ is
locally of finite type because $V_j\subset Y$ is an open subscheme and
$Y\to S$ is locally of finite type, and $V_j$ is affine over the
affine $W_j$; hence $B_j$ is a finitely generated
$\mathcal O(W_j)$-algebra.

We use the following elementary algebra fact. If
$A=\varinjlim_iA_i$ is a filtered colimit of $R$-algebras and
$A\to B$ is a surjection of $R$-algebras onto a finitely generated
$R$-algebra $B$, then $A_i\to B$ is surjective for all sufficiently
large $i$. Indeed, choose generators $b_1,\dots,b_n$ of $B$ over
$R$ and preimages $a_l\in A$ of the $b_l$, choose $i_l$ so that
$a_l$ lies in the image of $A_{i_l}$, and let
$i\ge i_1,\dots,i_n$: the composite $A_i\to A\to B$ is an
$R$-algebra homomorphism whose image contains $R$ and every $b_l$,
hence equals $B$.

Apply this to the surjection $A=\mathcal O(U_j)\to B_j$ over the ring
$\mathcal O(W_j)$: for each $j$ there is an index $i(j)$ such that
$A_i\to B_j$ is surjective for every $i\ge i(j)$, that is,
$V_j\to U_{i,j}$ is a closed immersion for every such $i$. Let $i$
be an index at least $\max_ji(j)$. For every $j$ the morphism
$V_j\to U_{i,j}$ is then a closed immersion, and
$V_j=Y\times_{X_i}U_{i,j}$ because fibre products are compatible with
the projections of the limit, so the morphism $Y\to X_i$ is affine by
[pqf-lem-affine-local-target] applied to the affine open covering
$X_i=\bigcup_jU_{i,j}$, and it is induced over $U_{i,j}$ by the
surjective ring homomorphism $A_i\to B_j$. By the definition of a
closed immersion in [def-weil-pbc-scheme-conventions] the morphism
$Y\to X_i$ is therefore a closed immersion.
