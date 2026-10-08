+++
id = "lem-sc-rigidity"
kind = "lemma"
title = "The rigidity lemma"
lean = ["AlgebraicGeometry.exists_eq_snd_comp"]
order = 490
uses = ["lem-sc-constant-locus-closed", "lem-sc-finite-image-locus-open"]
+++
Let $k$ be a field and $X,Y,Z$ schemes over $k$ with $X$ proper,
geometrically connected and geometrically reduced over $k$, $Y$
connected, and $Z$ separated and locally of finite type over $k$.
Let $f:X\times_kY\to Z$ be a morphism such that
$f(X\times\{y_0\})$ is a single point for some $k$-point
$y_0\in Y(k)$. Then $f$ factors through the projection
$X\times_kY\to Y$: there is a morphism $g:Y\to Z$ with
$f=g\circ\operatorname{pr}_2$.

## Proof

*Classical references: Milne, Abelian Varieties, Ch. I (the
rigidity lemma); Mumford, Abelian Varieties, II.6 (both over an
algebraically closed field).* The geometric hypotheses on $X$ cannot be
weakened to "connected and reduced". For $k=\mathbf R$, $X=\Spec\mathbf C$
(proper, connected, reduced, not geometrically connected),
$Y=\mathbf A^1_{\mathbf R}$, $Z=\mathbf A^1_{\mathbf C}$ viewed over
$\mathbf R$ and $f$ the identity of $X\times_kY=\mathbf A^1_{\mathbf C}$,
the fibre over $y_0=0$ is one point but $f$ does not factor through
$\operatorname{pr}_2$. For $\operatorname{char}k=p>0$, with
$X=\alpha_p=\Spec k[x]/(x^p)$ (proper and geometrically connected but
not reduced), $Y=Z=\mathbf A^1_k$ and $f(x,y)=y+x$, the set
$f(X\times\{0\})=\{0\}$ is a single point, yet $f$ does not factor
through $\mathbf A^1_k\to\mathbf A^1_k$ (the morphism $f$ is not the
pullback of any morphism of the $y$-line). Reducedness alone is not
enough either, i.e. *geometric* reducedness is needed: for $k$
imperfect of characteristic $p$, $a\in k\smallsetminus k^p$,
$k'=k(a^{1/p})$, $X=\Spec k'$ (proper, geometrically connected and
reduced, but not geometrically reduced), $Y=\mathbf A^1_k$,
$Z=\mathbf A^1_{k'}$ viewed over $k$ and $f$ the identity of
$X\times_kY=\mathbf A^1_{k'}$, the fibre over $y_0=0$ is one point and
Steps 1–3 below go through, but
$\operatorname{pr}_2:\mathbf A^1_{k'}\to\mathbf A^1_k$ is finite flat of
degree $p$, hence not a monomorphism, so $f=g\circ\operatorname{pr}_2$
is impossible; only Step 4 fails, as $\Gamma(X,\mathcal O_X)=k'\ne k$.

*Notation.* For $y\in Y$ let $f_y:X_{\kappa(y)}\to Z_{\kappa(y)}$ be the
fibre of $(f,\operatorname{pr}_2):X\times_kY\to Z\times_kY$ over $y$, and
$f_{\bar y}:X_{\overline{\kappa(y)}}\to Z_{\overline{\kappa(y)}}$ its base
change to an algebraic closure, as in
[lem-sc-constant-locus-closed] and [lem-sc-finite-image-locus-open].
Note $X\ne\emptyset$ (connected spaces are nonempty).

*Step 1: the locus of geometrically constant fibres is closed and
contains $y_0$.* Put

$$
L:=\{y\in Y: f_{\bar y}(X_{\overline{\kappa(y)}})\ \text{is a single point}\}.
$$

By [lem-sc-constant-locus-closed] applied to $X$, $Z$ and
$f$, the set $L$ is closed in $Y$. Moreover $y_0\in L$: since $y_0$ is
$k$-rational, $f_{y_0}$ is $f(-,y_0):X\to Z$, with image a single point
$z_0$. Choosing a closed point $x\in X$, we get $z_0=f(x,y_0)$, so
$\kappa(z_0)\subseteq\kappa(x)$ is finite over $k$, and the fibre of
$Z_{\bar k}\to Z$ over $z_0$, namely $\Spec(\kappa(z_0)\otimes_k\bar k)$,
is a finite discrete set. The image $f_{\bar y_0}(X_{\bar k})$ lies in
it and is connected, because $X_{\bar k}$ is connected ($X$ is
geometrically connected); hence it is a single point.

*Step 2: $L$ is open.* Let $y\in L$; then $f_y(X_{\kappa(y)})$ is the
image of the single point $f_{\bar y}(X_{\overline{\kappa(y)}})$, so it is
finite. By [lem-sc-finite-image-locus-open] (whose sole input is Stacks
Project, More on Morphisms, Lemma 37.44.3,
[Tag 0AH8](https://stacks.math.columbia.edu/tag/0AH8)) there is an
open neighbourhood $U_y\ni y$ such that $f_{y'}(X_{\kappa(y')})$ is
finite for every $y'\in U_y$. Fix such $y'$. The image
$f_{y'}(X_{\kappa(y')})$ is closed ($X_{\kappa(y')}$ is proper and
$Z_{\kappa(y')}$ separated) and finite in the scheme $Z_{\kappa(y')}$,
which is locally of finite type over $\kappa(y')$, hence Jacobson; so it
consists of closed points, whose residue fields are finite over
$\kappa(y')$. Each of them has finitely many preimages in
$Z_{\overline{\kappa(y')}}$, so $f_{\bar y'}(X_{\overline{\kappa(y')}})$
is finite, hence discrete. It is also connected, being the image of the
connected scheme $X_{\overline{\kappa(y')}}$; hence it is a single point,
i.e. $y'\in L$. Hence $L$ is open.

*Step 3: $L=Y$.* By Steps 1 and 2 the subset $L\subseteq Y$ is
open, closed and nonempty, while $Y$ is connected; hence
$L=Y$. Consequently, for every $y\in Y$ the set
$f(\operatorname{pr}_2^{-1}(y))$, which is the image in $Z$ of
$f_{\bar y}(X_{\overline{\kappa(y)}})$, is a single point $z_y$.

*Step 4: the factorization.* By Stacks Project, Varieties, Lemma 33.9.3
([Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)), since $X$ is
proper, geometrically connected and geometrically reduced over $k$, we
have $\Gamma(X,\mathcal O_X)=k$. Let $y\in Y$ and choose an affine open
$V\ni z_y$ of $Z$. The projection $\operatorname{pr}_2:X\times_kY\to Y$
is proper, hence closed, so
$Y\smallsetminus\operatorname{pr}_2\bigl(f^{-1}(Z\smallsetminus V)\bigr)$
is open; it contains $y$ because $f(\operatorname{pr}_2^{-1}(y))=\{z_y\}\subseteq V$.
Choose an affine open $U\ni y$ inside it; then
$f(X\times_kU)\subseteq V$. By flat base change along the flat map
$k\to\mathcal O(U)$ ($X$ is quasi-compact and separated),

$$
\Gamma(X\times_kU,\mathcal O)=\Gamma(X,\mathcal O_X)\otimes_k\mathcal O(U)=\mathcal O(U),
$$

the identification being $\operatorname{pr}_2^\#$. Since $V$ is affine,
$f|_{X\times_kU}:X\times_kU\to V$ corresponds to a ring map
$\mathcal O(V)\to\Gamma(X\times_kU,\mathcal O)=\mathcal O(U)$, i.e.
$f|_{X\times_kU}=g_U\circ\operatorname{pr}_2$ for the morphism
$g_U:U\to V\subseteq Z$ given by this ring map. Finally, the projection
$X\times_kY\to Y$ is faithfully flat ($X\ne\emptyset$) and
quasi-compact, hence an epimorphism in the category of schemes (fpqc
descent of morphisms); therefore on overlaps $U\cap U'$ the morphisms
$g_U$ and $g_{U'}$, both satisfying $f=g\circ\operatorname{pr}_2$ there,
agree. The $g_U$ thus glue to $g:Y\to Z$ with
$f=g\circ\operatorname{pr}_2$.
