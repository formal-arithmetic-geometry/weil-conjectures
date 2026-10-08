+++
id = "sbc-lem-bc-universal-test"
kind = "lemma"
title = "Universal curve-test datum for a failure"
order = 1396
uses = ["sbc-def-base-change-map", "sbc-def-base-change-property", "sbc-lem-bc-failure-field", "sbc-lem-bc-integral-base", "sbc-lem-bc-integral-surjective"]
+++
With $f:X\to S$ and $n$ as in [sbc-def-base-change-property] assume for
some $q\geq1$ that $\mathrm{BC}(f,n,q')$ holds universally for all
$q'\leq q-1$, but $\mathrm{BC}(f,n,q)$ does not hold universally. Then there exist a commutative diagram

$$
\begin{array}{ccccc}
X & \longleftarrow & X' & \longleftarrow & Y\\
f\big\downarrow & & \big\downarrow & & \big\downarrow h\\
S & \longleftarrow & S' & \longleftarrow & \operatorname{Spec}K
\end{array}
$$

with both squares Cartesian, where

1. $S'$ is affine, integral, and normal with algebraically closed
function field;
1. $K$ is algebraically closed and $\operatorname{Spec}K\to S'$ is
dominant (in other words $K$ is an extension of the function
field of $S'$),

and there exists an integer $d\mid n$ such that
$R^qh_*(\mathbf Z/d\mathbf Z)$ is nonzero.
(*Stacks Project, Lemma 59.88.7, [Tag `0F08`](https://stacks.math.columbia.edu/tag/0F08).*)

## Proof

By [sbc-lem-bc-failure-field] there are a morphism $S'\to S$ with
$S'$ affine, the base change $f':X'\to S'$, a field $K$ with a morphism
$T=\operatorname{Spec}K\to S'$, and a sheaf $\mathcal F$ on $T$
annihilated by $n$ for which the degree-$q$ base-change map of $f'$
along $T\to S'$ is not an isomorphism. By
[sbc-lem-bc-integral-surjective] (whose hypothesis, $\mathrm{BC}(f,n,q-1)$
universally, is part of ours) applied to
the base change $\pi:\operatorname{Spec}K'\to\operatorname{Spec}K$
to an algebraic closure $K'$ of $K$ (an integral surjective morphism),
we may assume $K$ is algebraically closed. A sheaf of
$\mathbf Z/n\mathbf Z$-modules on a geometric point is a direct sum of
copies of $\mathbf Z/d\mathbf Z$ for varying $d\mid n$, so by the
finite direct-sum and retract case of the map, we may assume
$\mathcal F$ is constant with value $\mathbf Z/d\mathbf Z$ for some
$d\mid n$ (the cokernel of the base-change map
$\bigl(R^qh_*(c)\bigr)$ decomposes accordingly). Finally, by
[sbc-lem-bc-integral-base] applied to
$\pi:S''\to S'$ the normalization of $S'$ in
$\operatorname{Spec}K$ (integral: the integral closure of the normal
domain $A'$ in $K$ is integral over $A'$, commutative algebra),
with $X''=X'\times_{S'}S''$, we may replace $S'$ by $S''$, which is
affine, integral, and normal with algebraically closed function field
$K$; this is the datum of the statement.
