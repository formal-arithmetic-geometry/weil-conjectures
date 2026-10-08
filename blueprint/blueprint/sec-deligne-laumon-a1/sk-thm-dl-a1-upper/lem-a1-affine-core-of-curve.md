+++
id = "lem-a1-affine-core-of-curve"
kind = "lemma"
title = "Affine core of a smooth curve"
order = 2804
uses = ["def-sc-curves", "def-weil-pbc-scheme-conventions", "lem-sc-affine-open-proper", "lem-sc-compactification"]
+++
Every smooth curve which is geometrically a connected curve has a nonempty dense affine
open whose complement is finite over the base field.

## Proof

Let $C_0$ be a smooth curve over $k_0$ which is geometrically a
connected curve. By
[lem-sc-compactification] there is a proper smooth curve
$\overline C$ and a dense open immersion $C_0\hookrightarrow\overline C$
with finite complement $S=\overline C\setminus C_0$. If
$S\neq\emptyset$, choose any closed point $s\in S$ and another
closed point $t\in\overline C\setminus\{s\}$ (a positive-dimensional
scheme of finite type over a finite field has infinitely many closed
points); put $V_0:=\overline C\setminus(S\cup\{t\})$, which is a dense
open of $C_0$ with nonempty complement in $\overline C$, hence
affine by [lem-sc-affine-open-proper] (its complement in the
proper smooth curve is a nonempty finite set). If $S=\emptyset$, i.e. $C_0=\overline C$ is proper, any closed point $s'\in C_0$ gives
$V_0:=C_0\setminus\{s'\}$ a dense open, again nonempty-complemented
and hence affine by the same lemma. In both cases $V_0$ is a
nonempty dense affine open of $C_0$ with finite complement.
