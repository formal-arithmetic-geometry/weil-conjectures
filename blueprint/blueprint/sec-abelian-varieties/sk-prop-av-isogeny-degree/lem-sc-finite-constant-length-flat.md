+++
id = "lem-sc-finite-constant-length-flat"
kind = "lemma"
title = "Finite morphisms with constant fibre length are flat"
order = 557
uses = ["def-sc-function-field"]
+++
Let $f:X\to Y$ be a finite surjective morphism of varieties over
a field $k$ such that the fibre length
$\dim_{k(y)}f_*\mathcal O_X\otimes k(y)$ is constant, equal to
$r$, as $y$ ranges over the closed points of $Y$. Then
$f$ is finite flat, $f_*\mathcal O_X$ is locally free of rank
$r$, and $\deg(f)=[k(X):k(Y)]$ of
function fields equals $r$.

## Proof

The fibre over the generic point $\eta$ of $Y$ is
$f^{-1}(\eta)=\operatorname{Spec}k(X)$ (a finite surjective
morphism of integral schemes is dominant, and over the generic
point the ring map is the field extension
$k(Y)\hookrightarrow k(X)$), so
$[k(X):k(Y)]=\dim_{k(Y)}k(X)$, the generic fibre length, and the
constant-length hypothesis forces $r=[k(X):k(Y)]=\deg(f)$. For
a closed point $y\in Y$, choose an affine open neighbourhood
$U=\operatorname{Spec}R$ of $y$ and elements
$s_1,\dots,s_r\in f_*\mathcal O_X(U)$ whose images form a
$k(y)$-basis of $f_*\mathcal O_X\otimes k(y)$; they define a
map $\mathcal O_U^{\oplus r}\to f_*\mathcal O_X|_U$ which is
surjective at $y$ and hence surjective on an open neighbourhood
$V\subseteq U$ of $y$ (Nakayama's lemma: *reference:
Stacks Project, Algebra, Lemma 10.20.1,
[Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)*). The
kernel $\mathcal K$ of $\mathcal O_V^{\oplus r}\to f_*\mathcal O_X|_V$ is a coherent sheaf with
$\mathcal K\otimes k(y)=0$ (the images of the $s_i$ form a
basis of the fibre, so the map on fibres is injective as well),
hence $\mathcal K=0$ on an open neighbourhood $W\subseteq V$
of $y$ (a coherent sheaf whose stalk at $y$ is zero vanishes
near $y$). Thus $\mathcal O_W^{\oplus r}\cong f_*\mathcal O_X|_W$: the set of points near which $f_*\mathcal O_X$ is locally free of rank $r$ is open and contains every
closed point and the generic point, hence is all of $Y$. So
$f_*\mathcal O_X$ is locally free of rank $r$, i.e. $f$ is
finite flat of degree $r$.
