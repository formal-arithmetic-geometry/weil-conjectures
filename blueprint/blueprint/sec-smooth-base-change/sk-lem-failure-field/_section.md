+++
id = "sk-lem-failure-field"
kind = "section"
title = "A failure is detected on the generic fibre"
order = 1387
uses = ["sk-def-bc"]
lean = ["AlgebraicGeometry.Etale.FieldFailure", "AlgebraicGeometry.Etale.nonempty_fieldFailure"]
+++
*Lemma (sketch).*

(Stacks Project, Lemma 59.88.6, Tag `0F07`.) Let $q\ge1$. If
$\mathrm{UBC}^{\le q-1}(f,n)$ holds ([sk-def-bc]: base change in
all degrees $\le q-1$, after every preliminary base change of $f$)
but $\mathrm{BC}(f,n,q)$ does not hold universally — it fails for
$f$ itself or for some base change $f_{S_1}$, $S_1\to S$ — then
there is a counterexample over a field: a morphism $S'\to S$ with
$S'$ an affine scheme (so that $S'\to S$ is an affine morphism when
$S$ is separated), the base change $f':X'=X\times_SS'\to S'$,
$T=\Spec K$ with $K$ a field and $g:\Spec K\to S'$, and a
$\Z/n\Z$-sheaf $\mathcal F$ on $\Spec K$ with
$f'^{-1}R^qg_*\mathcal F\to R^qh_*e^{-1}\mathcal F$ not an
isomorphism. (The conclusion concerns one degree after one
preliminary base change; the hypothesis has to be the universal
cumulative one, see the closed–open step of the proof.)

## Proof

Replacing $f$ by the base change $f_{S_1}$, which again satisfies
$\mathrm{UBC}^{\le q-1}$, we may assume that $\mathrm{BC}(f,n,q)$
itself fails. Let $g:T\to S$, $\mathcal F$ be a failing datum, so $g$ is a
quasi-compact quasi-separated *morphism* ([sk-def-bc]) but $T$
need not be a qcqs scheme, as [sk-lem-minimal] requires. Being an
isomorphism is local on $X$, and restriction to an affine open
$S'\subseteq S$ is pullback along an étale map, with which
$R^qg_*$, $R^qh_*$ and the base-change map commute; so the map already
fails over some affine open $S'$, and replacing $S$ by $S'$, $X$ by
$X\times_SS'$ and $T$ by $T\times_SS'$ we may assume $S$ affine (this
is the $S'$ of the statement). Now $T$, being qcqs over the affine
$S$, is a qcqs scheme. Apply [sk-lem-minimal] to the property ``the chosen cokernel
element survives'' (an element $\xi$ of the stalk of
$R^qh_*e^{-1}\mathcal F$ at a geometric point $\bar x$ not in the
image): it fails for the empty scheme, over which the stalk of
$R^qh_*e^{-1}\mathcal F$ is $0$, so the image of $\xi$ is $0$ and
lies in the image; thickenings do not change the étale site; limits work by
the limit theorem for higher direct images. For the closed–open
split let $i:Z\to T'$ be closed with quasi-compact open complement
$j:V\to T'$, and let $\mathcal J$ be an injective $\Z/n\Z$-sheaf on
$V$ containing $j^{-1}\mathcal F'$; the injectivity of
[sk-prop-injectivity] (2) applied to the embedding
$\mathcal F'\to j_*\mathcal J\oplus i_*i^{-1}\mathcal F'$ puts the
surviving element into one of the two summands. The closed summand
is handled by the exactness of $i_*$. For the open summand one
cannot use exactness of $j_*$, which fails in general
($R^1j_*(\Z/\ell)\neq0$ for $j:\gm\hookrightarrow\Aaf^1$); instead
let $e':Y'=X\times_ST'\to T'$ be the base change of $f$ along
$T'\to S$ and $j':V\times_{T'}Y'\to Y'$. The hypothesis
$\mathrm{UBC}^{\le q-1}(f,n)$ applied to $e'$ and the qcqs morphism
$j$ — this is where the property after a *preliminary* base
change, $T'\to S$, and in *all* degrees $\le q-1$ is consumed
— gives $e'^{-1}j_*\mathcal J\cong j'_*e_V^{-1}\mathcal J$ (degree
$0$) and $R^aj'_*e_V^{-1}\mathcal J\cong e'^{-1}R^aj_*\mathcal J=0$
for $1\le a\le q-1$ ($\mathcal J$ is injective). The relative Leray
spectral sequence for $h'\circ j'$ then makes
$R^qh'_*e'^{-1}j_*\mathcal J\to R^q(h'\circ j')_*e_V^{-1}\mathcal J$
injective, and [sk-prop-injectivity] (3) for the square of $f$
along $g'\circ j:V\to S$ and $j^{-1}\mathcal F'\subseteq\mathcal J$
shows that the element survives on $V$.

Uses: [sk-def-bc]
