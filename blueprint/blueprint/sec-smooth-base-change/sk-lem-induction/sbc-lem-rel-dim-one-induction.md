+++
id = "sbc-lem-rel-dim-one-induction"
kind = "lemma"
title = "The induction step in relative dimension one"
order = 1415
uses = ["def-sbc-smooth-morphisms", "sbc-def-base-change-property", "sbc-lem-bc-universal-test", "sbc-thm-universal-test-vanishing"]
+++
Let $f:X\to S$ be an affine smooth morphism of relative dimension one
with $X$ affine, let $n$ be an integer invertible on $S$, and assume, for some $q\geq1$, that
$\mathrm{BC}(f,n,q')$ holds universally for all $q'\leq q-1$ in the
sense of [sbc-def-base-change-property]. Then $\mathrm{BC}(f,n,q)$
holds universally, and hence $\mathrm{BC}(f,n,q')$ holds universally
for all $q'\leq q$.

## Proof

Suppose $\mathrm{BC}(f,n,q)$ does not hold universally. By
[sbc-lem-bc-universal-test] (whose hypothesis is the universal
cumulative $\mathrm{BC}(f,n,q')$, $q'\leq q-1$, assumed here) there is
a universal curve test datum: after base
change and normalization, $X'=X\times_SS'\to S'$ is a base change of
$f$ with $S'$ affine, hence (affine smooth morphisms of relative
dimension one being stable under base change, as is immediate from
[def-sbc-smooth-morphisms])
affine smooth of relative dimension one with $X'$ affine, $S'$ is the
spectrum of a normal domain with algebraically closed fraction field
$L$, $K/L$ an extension of algebraically closed fields, and for some
$d\mid n$ the sheaf $R^qh_*(\mathbf Z/d\mathbf Z)$ is nonzero. This
contradicts [sbc-thm-universal-test-vanishing], whose hypotheses
hold: $d$ is invertible on $S'$ because $d\mid n$ and $n$ is invertible
on $S$ and on all its base changes (the $\mathrm{BC}$-property
being a statement about base changes of
$f$); the normalization $S''\to S'$ in $\operatorname{Spec}K$ is
integral because the integral closure of the domain $A'$ in $K$ is
integral over $A'$ (commutative algebra). Hence $\mathrm{BC}(f,n,q)$
holds universally. (Equivalently: the hypotheses of the lemma are
inherited by every base change $f'$ of $f$ with affine source, and the
class of smooth morphisms of relative dimension $\leq1$ is stable under
base change, so the induction produces the universal form.)
