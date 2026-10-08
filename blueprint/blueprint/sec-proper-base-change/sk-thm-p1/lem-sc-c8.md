+++
id = "lem-sc-c8"
kind = "lemma"
title = "C8: surjectivity of the restriction map in degree two"
order = 1119
uses = ["def-sc-curves", "def-weil-pbc-eight-curve-assertions", "def-weil-pbc-scheme-conventions", "lem-sc-affine-cohomological-dimension", "lem-sc-affine-open-proper", "lem-sc-compactification", "thm-sc-affine-cohomology"]
+++
Let $k$ be algebraically closed, let $C$ be a
smooth separated connected curve over $k$, let
$j:U\hookrightarrow C$ be an
open immersion, and let
$r$ be a prime. Then the constant sheaf $\mathbf F_r$ satisfies
$\mathcal C_8(C,\mathbf F_r)$ of
[def-weil-pbc-eight-curve-assertions]: the restriction map

$$
H^2(C_{\Et},\mathbf F_r)\longrightarrow
H^2(U_{\Et},\mathbf F_r)
$$

is surjective.

## Proof

By [lem-sc-compactification] and [lem-sc-affine-open-proper],
either $C$ is proper, or $C$ is affine. If $C$ is proper and
$U=C$, the map is the identity. If $C$ is proper and
$U\subsetneq C$, then $U$ is affine by
[lem-sc-affine-open-proper], hence
$H^2(U,\mathbf F_r)=0$ by
[lem-sc-affine-cohomological-dimension] (or
[thm-sc-affine-cohomology] for $r\neq\operatorname{char}k$);
the map from an abelian group to $0$ is surjective. If $C$ is
affine, then $H^2(C,\mathbf F_r)=0$ and the map is trivially
surjective.
