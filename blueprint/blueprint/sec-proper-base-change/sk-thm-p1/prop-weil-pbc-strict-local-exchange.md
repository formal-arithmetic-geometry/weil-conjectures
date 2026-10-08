+++
id = "prop-weil-pbc-strict-local-exchange"
kind = "theorem"
title = "Strict-local projective-line exchange"
order = 1143
uses = ["def-weil-pbc-derived-exchange", "def-weil-pbc-henselian-terminology", "prop-weil-pbc-p1-strict-henselian-comparison"]
tags = ["latex:proposition"]
+++
Let $A\to B$ be a local morphism of strictly henselian local rings inducing a
specified extension of their separably closed residue fields. For the
base-change square of $\mathbf P^1_A\to\operatorname{Spec}A$, the stalk of the
exchange morphism [def-weil-pbc-derived-exchange] at the closed geometric
point of $\operatorname{Spec}B$ is the restriction map between the
cohomologies of the two closed projective lines. If the residue-field map is
an isomorphism, this stalk map is an isomorphism.

## Proof

On a termwise injective representative of the exchange morphism of
[def-weil-pbc-derived-exchange], the stalk at the closed geometric point is
computed by applying the comparison of
[prop-weil-pbc-p1-strict-henselian-comparison] to the two closed fibres; expanding
the unit--$\theta_\square$--counit composite shows that this is the
restriction map between the cohomologies of the two closed projective lines,
which is an isomorphism when the residue-field map is an isomorphism.
