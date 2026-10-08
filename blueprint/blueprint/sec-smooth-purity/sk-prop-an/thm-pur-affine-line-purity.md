+++
id = "thm-pur-affine-line-purity"
kind = "theorem"
title = "Affine-line purity"
order = 1975
uses = ["cor-amb-affine-space-adjunction", "def-amb-p1-trace", "def-pur-affine-line-datum", "def-pur-affine-line-purity-comparison", "def-pur-conventions", "prop-asd-smooth-base-change", "thm-pur-affine-line-orientation", "thm-sf-ambient-adjoint-class", "thm-weil-pbc-site-comparison"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting), let $Y$ be the scheme of the
affine-line datum and let
$K\in D^b_{ctf}(Y,\Lambda)$ with $\Lambda=A$. The affine-line purity
comparison $\gamma_{p,K}$ of
[def-pur-affine-line-purity-comparison] – the adjoint of the
projection-formula composite
$Rp_!Lp^*K(1)[2]\cong K\otimes^L Rp_!\Lambda_{\mathbf A^1_Y}(1)[2]\to K$
formed with the projective-line trace and normalized by the orientation
$\operatorname{pur}_s$ of [thm-pur-affine-line-orientation] – is an isomorphism

$$
\gamma_{p,K}:Lp^*K(1)[2]\xrightarrow{\ \sim\ }Rp^!K.
$$

It is natural in $K$ and compatible with arbitrary base change of $Y$.
(Source: the relative affine-line case of cohomological purity, as in
Milne, Lectures on Etale Cohomology, Section 16, Theorems 16.1 and
16.7 and Proposition 16.11, with the acyclicity computation of Example
16.3 and the Gysin sequence of the divisor, over an arbitrary base
scheme.)

## Proof

On the ordinary etale site, [cor-amb-affine-space-adjunction]
constructs $Rp_!\dashv p^*(1)[2]$ by composing
$j_!\dashv j^*$ with the explicit projective-line adjunction.
Its counit is exactly the composite in
[def-pur-affine-line-purity-comparison], since
[def-amb-p1-trace] defines the same normalized trace.
Uniqueness of a right adjoint with its counit therefore identifies its
adjoint $\gamma_{p,K}$ with an isomorphism.
The actual-adjoint comparison of [thm-sf-ambient-adjoint-class]
and [thm-weil-pbc-site-comparison] transport this statement and
the adjunction bijection to the finite etale-origin coefficients of
this chapter. Naturality follows from the defining adjunction.
For base change, [prop-asd-smooth-base-change] identifies the mate
of compact-support base change with the inverse-image and twist
identification for this explicit affine-line adjunction. Hence the
same defining counit, and therefore $\gamma_{p,K}$, commutes with
arbitrary base change. General smooth purity is not an input here.
