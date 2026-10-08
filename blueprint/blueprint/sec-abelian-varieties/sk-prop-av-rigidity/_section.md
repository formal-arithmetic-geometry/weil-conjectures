+++
id = "sk-prop-av-rigidity"
kind = "section"
title = "The rigidity lemma"
lean = ["AlgebraicGeometry.exists_eq_snd_comp"]
order = 489
uses = ["sk-prop-av-const-locus", "sk-prop-av-image-open"]
+++
*Proposition (sketch).*

Let $X,Y,Z$ be $k$-schemes with $X$ proper, geometrically connected
and geometrically reduced over $k$, $Y$ connected, $Z$ separated and
locally of finite type over $k$, and let $f:X\times_kY\to Z$ be a
morphism with $f(X\times\{y_0\})$ a single point for some
$y_0\in Y(k)$. Then $f$ factors through the projection:
$f=g\circ\mathrm{pr}_2$ for some $g:Y\to Z$. (Both geometric
hypotheses are needed. For $k=\mathbf R$, $X=\Spec\mathbf C$,
$Y=\mathbf A^1_{\mathbf R}$, $Z=\mathbf A^1_{\mathbf C}$ and $f=\mathrm{id}$ of
$X\times_kY=\mathbf A^1_{\mathbf C}$, $X$ is connected, reduced and even
geometrically reduced, but not geometrically connected, and $f$ does
not factor. For $k$ imperfect of characteristic $p$,
$a\in k\smallsetminus k^p$, $k'=k(a^{1/p})$, $X=\Spec k'$,
$Y=\mathbf A^1_k$, $Z=\mathbf A^1_{k'}$ and $f=\mathrm{id}$ of
$X\times_kY=\mathbf A^1_{k'}$, $X$ is geometrically connected and
reduced, but not geometrically reduced; here
$\mathrm{pr}_2:\mathbf A^1_{k'}\to\mathbf A^1_k$ is finite flat of degree
$p$, hence not a monomorphism, so $f=g\circ\mathrm{pr}_2$ is impossible,
although Steps 1–3 of the proof below go through and only Step 4
fails, as $\Gamma(X,\mathcal O_X)=k'\ne k$.)

## Proof

Notation $f_y$, $f_{\bar y}$ as in [sk-prop-av-const-locus] and [sk-prop-av-image-open].
*Step 1.* $L=\{y: f_{\bar y}(X_{\overline{\kappa(y)}})\ \text{is a point}\}$ is
closed by [sk-prop-av-const-locus] ($X\ne\emptyset$, being
connected). It contains $y_0$: the point
$z_0=f(X\times\{y_0\})$ is the image of a closed point of $X$, so
$\kappa(z_0)$ is finite over $k$ and the fibre of
$Z_{\bar k}\to Z$ over $z_0$ is finite; the connected $X_{\bar k}$
maps into it, hence to one point.
*Step 2.* If $y\in L$, then $f_y(X_{\kappa(y)})$ is a point, so by
[sk-prop-av-image-open] there is an open $U_y\ni y$ with
$f_{y'}(X_{\kappa(y')})$ finite for all $y'\in U_y$; it consists of
closed points of $Z_{\kappa(y')}$ (with residue fields finite over
$\kappa(y')$), so $f_{\bar y'}(X_{\overline{\kappa(y')}})$ is finite too, and
as $X_{\overline{\kappa(y')}}$ is connected (geometric connectedness) and a
finite set is discrete, it is a point: $L$ is open.
*Step 3.* $L$ is nonempty, open and closed in the connected $Y$,
hence $L=Y$: for every $y$, $f(\mathrm{pr}_2^{-1}(y))$ is a single
point $z_y$.
*Step 4.* Since $X$ is proper, geometrically connected and
geometrically reduced, $\Gamma(X,\mathcal O_X)=k$ (`0BUG`). Given $y$,
choose an affine open $V\ni z_y$; as $\mathrm{pr}_2$ is closed,
$Y\smallsetminus\mathrm{pr}_2(f^{-1}(Z\smallsetminus V))$ is an open
neighbourhood of $y$, containing an affine open $U\ni y$ with
$f(X\times_kU)\subseteq V$. By flat base change
$\Gamma(X\times_kU,\mathcal O)=\Gamma(X,\mathcal O_X)\otimes_k\mathcal O(U)=\mathcal O(U)$, so
$f|_{X\times_kU}$, given by $\mathcal O(V)\to\mathcal O(U)$, equals
$g_U\circ\mathrm{pr}_2$ for some $g_U:U\to V$. As $\mathrm{pr}_2$ is faithfully flat and
quasi-compact, hence an epimorphism of schemes, the $g_U$ are unique
and glue to $g:Y\to Z$ with $f=g\circ\mathrm{pr}_2$.

Uses: [sk-prop-av-const-locus], [sk-prop-av-image-open]
