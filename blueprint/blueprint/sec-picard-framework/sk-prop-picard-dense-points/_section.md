+++
id = "sk-prop-picard-dense-points"
kind = "section"
title = "Zariski density of rational points"
order = 746
uses = ["sk-def-av-jacobian", "sk-def-av-pic"]
lean = ["AlgebraicGeometry.Scheme.Hom.denseRange_fieldPoints"]
+++
*Proposition (sketch).*

Let $X$ be a smooth scheme over a separably closed field $k$ with
$X(k)\neq\emptyset$. Then $X(k)$ is Zariski dense in $X$; in
particular, for a smooth projective curve $X$ over separably closed
$k$, the set $X(k)$ is infinite (and, by density, for every
non-zero global section of a line bundle on $X_K$, $K=k$ or a
field extension, there is $x\in X(k)$ at which the section does not
vanish, provided it does not vanish identically).

## Proof

*Step 1 (rationally defined closed points are dense).* Over any
field $k$, a smooth $X$ has a dense set of closed points $x$ with
$\kappa(x)/k$ finite separable. The claim is Zariski-local, so it is
enough to find one such point in each nonempty open $V$. Smoothness
makes some nonempty open $U\subseteq V$ admit an étale
$\pi:U\to\mathbf A^d_k$: a standard smooth presentation
$k[x_1,\dots,x_n]/(f_1,\dots,f_c)$ has an invertible Jacobian
subdeterminant, which says exactly that the projection to the remaining
$n-c$ coordinates is étale. Étale morphisms are open, so $\pi(U)$
is a nonempty open of $\mathbf A^d_k$; shrinking it to a complement
$\mathbf A^d_k\setminus V(f)$ with $f\ne0$ and using that
$k^{\mathrm{sep}}$ is infinite, $f$ cannot vanish at every
$(a_1,\dots,a_d)\in(k^{\mathrm{sep}})^d$, which produces a closed point
$w\in\pi(U)$ with $\kappa(w)/k$ finite separable. Any $x\in U$ over $w$
has $\kappa(x)/\kappa(w)$ finite separable, $\pi$ being étale hence
unramified, so $\kappa(x)/k$ is finite separable; and $x$ is closed
because a point whose residue field is finite over $k$ on a scheme
locally of finite type over $k$ is closed.

*Step 2 (separable closedness).* A finite separable extension
$K/k$ of a separably closed field is trivial: it is simple,
$K=k[\alpha]$, and the minimal polynomial of $\alpha$ is irreducible and
separable, hence has a root in $k$, hence is linear. So the points of
Step 1 satisfy $\kappa(x)=k$, i.e. they are $k$-rational, and $X(k)$ is
dense. In particular $X(k)\ne\emptyset$ as soon as $X\ne\emptyset$, so
that hypothesis of the statement is automatic.

*Step 3 (a curve has infinitely many rational points).* On a
smooth projective curve a finite set of closed points is not dense, $X$
being integral of dimension one, so Step 2 forces $X(k)$ to be infinite.
For a field extension $K/k$ and $x\in X(k)$ the pullback
$x_K=\Spec K\times_kx$ is a $K$-rational point of $X_K$, and the family
$(x_K)_{x\in X(k)}$ is Zariski dense in $X_K$: it is infinite and $X_K$
is again an integral curve, so a closed subset containing infinitely
many closed points is all of $X_K$.

*Step 4 (non-vanishing).* For $0\ne s\in H^0(X_K,\cL)$ the germ of
$s$ at the generic point is nonzero, $X_K$ being integral, so the zero
scheme $Z(s)$ is a proper closed subset of a one-dimensional Noetherian
scheme and hence a finite set of closed points. By Step 3 there is an
$x\in X(k)$ with $x_K\notin Z(s)$, i.e. $s$ does not vanish at $x_K$.

Steps 1–2 are Blueprint 50, `lem-pc-rational-points-dense`,
resting on `lem-pc-dense-separable-points` (Stacks, Varieties,
Lemma 33.25.6, [`056U`](https://stacks.math.columbia.edu/tag/056U)) and
`lem-pc-sepclosed-finite-sep-trivial`; Steps 3–4 are Step 3 of
`lem-pc-twist` there.
