+++
id = "prop-weil-pbc-scalar-extension"
kind = "theorem"
title = "Compatibility with finite scalar extension"
order = 1307
uses = ["def-weil-pbc-rational-category"]
tags = ["latex:proposition"]
+++
For a finite extension $E\subset E'$, derived scalar extension is an exact
functor
$$
 T_{E'/E}=E'\otimes_E^L-:
 \Dbc(T,E)\longrightarrow\Dbc(T,E').
$$
Choose $T_{E/E}=\operatorname{id}$ literally. For $E\subset E'\subset E''$,
derived tensor associativity gives a specified exact natural isomorphism
$$
 a_{E'',E',E}:T_{E''/E'}T_{E'/E}
 \xrightarrow{\sim}T_{E''/E}.
$$
These associators satisfy the unit equations and the pentagon for four
nested fields. Exactness supplies natural shift comparisons
$$
 \sigma_{E'/E,K}:T_{E'/E}(K[1])
 \xrightarrow{\sim}(T_{E'/E}K)[1]
$$
which commute with the associators.

There are coherent natural isomorphisms
$$
 E'\otimes_E^LRf_{*,E}K\xrightarrow{\sim}
 Rf_{*,E'}(E'\otimes_E^LK)
$$
and analogous isomorphisms for pullback. Under these isomorphisms, scalar
extension of the $E$-exchange map is the $E'$-exchange map.

*Source:* the coherent scalar-extension package for finite coefficient
fields, i.e. the coefficient-extension formalism of derived complete torsion
coefficients: the exactness is the flatness of a finite field extension, and
the associators, shift comparisons and the direct-image and pullback
compatibilities are the standard derived-tensor-associativity and
projection-formula identifications of the formalism, as in Milne, *Lectures
on Etale Cohomology*, Section 19 (finiteness theorems; sheaves of
$\mathbf Z_\ell$-modules); no Stacks Project tag is recorded for this
package.

## Proof

This is the recorded input of the statement, the coherent scalar-extension
package of the adic formalism (Milne, *Lectures on Étale Cohomology*,
Section 19; no Stacks Project tag is recorded for it). Its two elementary
ingredients are named in the statement itself: exactness is the flatness of
a finite field extension, and the associators, unit equations and pentagon
are the coherence of the derived tensor product, transported along the exact
functor $E'\otimes_E^-$. The blueprint uses the package as the definition of
the coefficient extension between the $E$- and $E'$-stages of
[def-weil-pbc-rational-category]; no separate proof is given.
