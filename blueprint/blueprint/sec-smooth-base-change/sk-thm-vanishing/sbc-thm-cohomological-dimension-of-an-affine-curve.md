+++
id = "sbc-thm-cohomological-dimension-of-an-affine-curve"
kind = "theorem"
title = "Affine-curve cohomological dimension"
order = 1411
uses = ["def-weil-pbc-etale-cohomology", "def-weil-pbc-scheme-conventions", "thm-sc-affine-cohomology"]
+++
Let $k$ be algebraically closed, let $C$ be a
smooth affine curve over
$k$, and let $d\geq1$ be prime to $\operatorname{char}k$. Then

$$
H^q(C_{\Et},\mathbf Z/d\mathbf Z)=0\qquad(q>1)
$$

with $H^0(C_{\Et},\mathbf Z/d\mathbf Z)=\mathbf Z/d\mathbf Z$.
(*the Jacobian chapter, [thm-sc-affine-cohomology]; Stacks Project,
Theorem 59.83.10, [Tag `03SC`](https://stacks.math.columbia.edu/tag/03SC), (2).*)

## Proof

The cohomology groups of [def-weil-pbc-etale-cohomology] of the
constant sheaf $\mathbf Z/d\mathbf Z$ are computed in
[thm-sc-affine-cohomology] of the Jacobian chapter (with
$n=d$), where the vanishing for $q>1$ is displayed under the
identifications of the Kummer sequence; this is the claim.
