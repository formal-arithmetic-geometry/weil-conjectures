+++
id = "sk-prop-av-image-open"
kind = "section"
title = "Finiteness of the image is open in the parameter"
lean = ["AlgebraicGeometry.eventually_finite_image"]
order = 487
uses = ["sk-def-av"]
+++
*Proposition (sketch).*

Let $X$ be proper over $k$, $Z$ separated and locally of finite type
over $k$, $f:X\times_kY\to Z$ a morphism and $y_0\in Y$; for $y\in Y$
write $f_y:X_{\kappa(y)}\to Z_{\kappa(y)}$ for the fibre of
$(f,\mathrm{pr}_2):X\times_kY\to Z\times_kY$ over $y$. If
$f_{y_0}(X_{\kappa(y_0)})$ is finite, then $f_y(X_{\kappa(y)})$ is finite
for all $y$ in an open neighbourhood of $y_0$.

## Proof

Apply `0AH8` (valid at an arbitrary point $s$ of the base) to
the triangle over $S=Y$ formed by
$p=\mathrm{pr}_2:X\times_kY\to Y$, $q=\mathrm{pr}_2:Z\times_kY\to Y$
and $h=(f,p)$. Here $p$ is proper (base change of $X\to\Spec k$) and
$q$ is separated and locally of finite type, and the fibre $h_{y_0}=f_{y_0}$
has finite image by hypothesis; loc. cit. gives an open
$U\ni y_0$ and a closed subscheme $W\subseteq Z\times_kU$ finite over
$U$ through which $h$ factors, so $f_y(X_{\kappa(y)})\subseteq W_y$ is
finite for every $y\in U$.

Uses: [sk-def-av]
