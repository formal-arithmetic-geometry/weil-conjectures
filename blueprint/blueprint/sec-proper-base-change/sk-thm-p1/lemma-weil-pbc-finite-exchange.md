+++
id = "lemma-weil-pbc-finite-exchange"
kind = "lemma"
title = "Finite exchange isomorphism"
order = 1121
lean = ["AlgebraicGeometry.Etale.isBaseChangeIso_of_isFinite", "AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite"]
uses = ["def-kun-separably-closed", "def-weil-pbc-cartesian-square", "def-weil-pbc-derived-exchange", "def-weil-pbc-geometric-fibre", "def-weil-pbc-property", "def-weil-pbc-scheme-conventions", "def-weil-pbc-underived-exchange", "lemma-openclosed-point-ulift", "lemma-openclosed-stalk-upperstar", "lemma-weil-pbc-finite-direct-image-exact", "lemma-weil-pbc-finite-stalk-formula", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
For a finite Cartesian square, the underived exchange map is an isomorphism;
therefore all its derived exchange maps are isomorphisms.

## Proof

At a geometric point $\bar y'\to Y'$, the fibre of $f'$ is the base change of
the finite fibre of $f$ along $\kappa(\bar y)\to\kappa(\bar y')$. The stalk
formula identifies both sides with the same finite product indexed by these
points, and the exchange map is the identity on each factor. Thus it is a
stalkwise bijection and hence an isomorphism. Exactness from the preceding
lemma means injective resolutions remain direct-image acyclic, so the same
degreewise argument computes the derived map.

## Detailed form

In a cartesian square with $f$ finite, the underived exchange map is the
bijection obtained by base changing the finite geometric fiber:

$$
 g^{-1}f_*F\xrightarrow{\sim}f'_*g'^{-1}F.
$$

The isomorphism is compatible with the stalk formula on both sides, and the
derived exchange morphism [def-weil-pbc-derived-exchange] is an isomorphism.

## Proof

At a geometric point $\bar y'\to Y'$, the two underived sides identify, via
[lemma-weil-pbc-finite-stalk-formula], with the same finite direct sum of stalks
indexed by the geometric points of the finite fibre; expanding the
unit--$\theta_\square$--counit composite of
[def-weil-pbc-underived-exchange] shows that the induced map is the identity
on every summand, hence an isomorphism. By
[lemma-weil-pbc-finite-direct-image-exact] both direct images are exact, so the
same degreewise comparison computes the derived exchange morphism.
