+++
id = "lem-sc-proper-affine-finite"
kind = "lemma"
title = "Proper affine curves are finite"
order = 921
uses = ["def-sc-curves", "lem-weil-pbc-proper-closed-image", "pqf-lem-image-proper"]
+++
Let $C$ be a curve over $k$ which is
both proper and affine over $k$. Then $C$ is finite over $k$
(in particular of dimension zero).

## Proof

Write $C=\operatorname{Spec}B$ with $B$ a $k$-algebra of finite
type. If $B$ were not finite over $k$, then $B$ would contain
an element $t$ transcendental over $k$ (a finitely generated
$k$-algebra all of whose elements are algebraic over $k$ is a
finite-dimensional $k$-vector space). The $k$-algebra map
$k[x]\to B$, $x\mapsto t$, defines a morphism
$\varphi:\operatorname{Spec}B\to\mathbf A^1_k$. Since
$\operatorname{Spec}B$ is proper over $k$, the image
$Z:=\varphi(\operatorname{Spec}B)$ is a closed subscheme of
$\mathbf A^1_k$ which is proper over $k$, by [lem-weil-pbc-proper-closed-image] of the ambient-foundations chapter and [pqf-lem-image-proper] of the quasi-finite chapter). Now $Z\neq\mathbf A^1_k$: the affine
line is not proper over $k$, because the image of the closed
subset $V(xy-1)\subset\mathbf A^1_k\times_k\mathbf A^1_k$ under
the first projection is $\mathbf A^1_k\setminus\{0\}$, which is
not closed. Hence $Z=V(f)$ for a nonzero $f\in k[x]$, a finite
set of closed points. But $Z$ is also the closed subscheme of
$\mathbf A^1_k$ cut out by the kernel of the map $k[x]\to B$, and
this kernel contains no nonzero polynomial because $t$ is
transcendental, so $Z=\mathbf A^1_k$, a contradiction. Therefore
$B$ is integral over $k$, and being of finite type it is finite
over $k$. A finite $k$-scheme has dimension zero: every quotient
of a finite $k$-algebra is finite over $k$, and a domain finite
over the field $k$ is a field.
