+++
id = "lem-sc-finite-image-locus-open"
kind = "lemma"
title = "Finiteness of the image is an open condition on the parameter"
lean = ["AlgebraicGeometry.eventually_finite_image"]
order = 488
+++
Let $k$ be a field, $X$ a $k$-scheme proper over $k$, $Z$ a
$k$-scheme separated and locally of finite type over $k$, $Y$ a
$k$-scheme, $f:X\times_kY\to Z$ a morphism and $y_0\in Y$ (an
arbitrary point, not necessarily $k$-rational). For $y\in Y$ write

$$
f_y:X_{\kappa(y)}\longrightarrow Z_{\kappa(y)}
$$

for the fibre over $y$ of $(f,\operatorname{pr}_2):X\times_kY\to Z\times_kY$.
If $f_{y_0}(X_{\kappa(y_0)})$ is finite, then there is an open
neighbourhood $U\subseteq Y$ of $y_0$ such that $f_y(X_{\kappa(y)})$ is
finite for every $y\in U$.

## Proof

Apply Stacks Project, More on Morphisms, Lemma 37.44.3
([Tag 0AH8](https://stacks.math.columbia.edu/tag/0AH8)), which is
stated at an arbitrary point $s$ of the base, to the
commutative triangle over $S:=Y$ formed by the two morphisms
$p=\operatorname{pr}_2:X\times_kY\to Y$,
$q=\operatorname{pr}_2:Z\times_kY\to Y$ and
$h=(f,p):X\times_kY\to Z\times_kY$, so that $q\circ h=p$.
The hypotheses of loc. cit. hold at $s=y_0$:
$p$ is the base change of the proper morphism $X\to\Spec k$, hence
proper; $q$ is separated (it is the base change of
$Z\to\Spec k$, which is separated) and locally of finite type (the
base change of $Z\to\Spec k$, which is locally of finite type); and
the fibre $h_{y_0}=f_{y_0}:X_{\kappa(y_0)}\to Z_{\kappa(y_0)}$ has
finite image by hypothesis.
Loc. cit. therefore gives an open $U\ni y_0$ and a closed
subscheme $W\subseteq Z\times_kU$ finite over $U$ such that
$h|_{X\times_kU}$ factors through $W$. For $y\in U$ the set
$f_y(X_{\kappa(y)})$ is contained in the fibre $W_y$, which is finite
over $\kappa(y)$; hence $f_y(X_{\kappa(y)})$ is finite.
