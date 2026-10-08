+++
id = "prop-galois-weight-strata-identification"
kind = "theorem"
title = "Identification of the stratum root multisets"
order = 2908
tags = ["latex:proposition"]
uses = ["def-weil-normalized-integral-fraction", "def-weil-numbers", "def-weil-ordinary-reciprocal-roots", "prop-galois-weight-strata"]
+++
In the situation of [prop-galois-weight-strata], for every integer
$i$ with $0\leq i\leq2d$ the
reciprocal-root multiset of
$Q_i$, equivalently the root multiset of
$Q_i^\#(U)=U^{\deg Q_i}Q_i(U^{-1})$, is exactly the submultiset of the
roots of $A^\#$ satisfying the weight-$i$
$q$-Weil condition when $i$ is odd, and
exactly the submultiset of the roots of $B^\#$ satisfying that condition
when $i$ is even; the multiset is therefore determined by the weight
condition alone and does not depend on the ordering of the roots.

## Proof

The reciprocal-root multiset of $Q_i$ is the root multiset of the monic
polynomial

$$
Q_i^\#(U)=U^{\deg Q_i}Q_i(U^{-1})
=\prod_{\alpha\in R_i}(U-\alpha),
$$

in the convention of [def-weil-ordinary-reciprocal-roots], and by the
definition of $R_i$ – the submultiset of roots of $A^\#$ for $i$
odd and of $B^\#$ for $i$ even satisfying the weight-$i$ $q$-Weil
condition – this is exactly the asserted submultiset; since each root has
a unique weight by assumption, the submultiset does not depend on the
ordering of the roots. The normalized presentation used here is the one
of [def-weil-normalized-integral-fraction].
