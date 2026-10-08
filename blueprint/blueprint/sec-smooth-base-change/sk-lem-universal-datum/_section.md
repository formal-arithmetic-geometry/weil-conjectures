+++
id = "sk-lem-universal-datum"
kind = "section"
title = "Universal curve-test datum for a failure"
order = 1392
uses = ["sk-def-bc", "sk-def-smooth"]
lean = ["AlgebraicGeometry.Etale.CurveTestDatum", "AlgebraicGeometry.Etale.exists_curveTestDatum"]
+++
*Lemma (sketch).*

(Stacks Project, Lemma 59.88.7, Tag `0F08`.) Let $q\ge1$. If
$\mathrm{UBC}^{\le q-1}(f,n)$ holds but $\mathrm{BC}(f,n,q)$ does not
hold universally ([sk-def-bc]), then
there is a universal curve-test datum: a morphism $S'\to S$ and a
Cartesian square

$$
\begin{array}{ccc}
X'=X\times_SS' & \xleftarrow{\;h\;} & Y\\
f'\downarrow & & \downarrow e\\
S' & \xleftarrow{\;g\;} & \Spec K
\end{array}
$$

with $S'=\Spec A$ affine, integral, normal, fraction field $L$
algebraically closed, $K/L$ an extension of algebraically closed
fields, $f'$ the base change of $f$, and an
integer $d\mid n$ such that

$$
R^qh_*(\Z/d\Z)\ \neq\ 0 .
$$

The lemma asserts nothing about the geometry of $f'$ beyond its being
a base change of $f$: properties of $f$ that are stable under base
change (affine, smooth, of relative dimension one) are inherited by
$f'$, and this is how [sk-lem-induction] obtains the datum
required by [sk-thm-vanishing]; they are not produced by the lemma.

## Proof

By [sk-lem-failure-field] one works over a field $K$ and an affine
$S'$ (a preliminary base change of $f$); an integral
surjective base change to an algebraic closure of $K$ preserves the
failure (surjectivity on a geometric point makes the same element
survive; this uses $\mathrm{BC}(f',n,q-1)$, part of the hypothesis),
so $K$ is algebraically closed; a
$\Z/n\Z$-module on a geometric point is a sum of $\Z/d\Z$'s, so one
passes to a constant $\Z/d\Z$ with $d\mid n$; finally the
normalization of $S'$ in $\Spec K$ is integral, so the
integral base-change lemma gives the normal $S'$ (its $X'$ is again
a base change of $f$).

Uses: [sk-def-bc], [sk-def-smooth]
