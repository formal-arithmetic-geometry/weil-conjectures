+++
id = "lem-exc-closed-site-adjunction"
kind = "lemma"
title = "Adjunction for the closed-site lift"
order = 1844
uses = ["def-exc-closed-site-lift", "lem-exc-closed-lift-adjunction", "lem-exc-closed-lift-reduction"]
+++
The functor $v$ is left adjoint to $u$, with $uv$ canonically the identity,
for the functors of [def-exc-closed-site-lift].

## Proof

The adjunction of [def-exc-closed-site-lift] is the opposite of
[lem-exc-closed-lift-adjunction], and its unit is an isomorphism by
[lem-exc-closed-lift-reduction]. The triangle identities are those of the
algebra adjunction with arrows reversed.
