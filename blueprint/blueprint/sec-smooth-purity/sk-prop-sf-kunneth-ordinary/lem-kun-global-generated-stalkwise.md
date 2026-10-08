+++
id = "lem-kun-global-generated-stalkwise"
kind = "lemma"
title = "Global generation is stalkwise surjectivity"
order = 1692
uses = ["def-kun-constant-sheaf", "def-kun-global-generated", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-geometric-stalks-exact"]
+++
Let $T$ be a scheme, $\Lambda$ a commutative ring and $F$ a sheaf
of $\Lambda_T$-modules on $T_{\Et}$, with evaluation morphism
$\bigoplus_{s\in\Gamma(T_{\Et},F)}\underline{\Lambda}\to F$ of
[def-kun-global-generated]. Then the following are equivalent:

1. **(1)** $F$ is globally generated, i.e. the evaluation morphism
is an epimorphism of sheaves;
1. **(2)** the evaluation morphism is surjective on every geometric
stalk of $T$.

## Proof

The stalk functors are exact by
[prop-weil-pbc-geometric-stalks-exact], so the geometric stalks of
the cokernel of the evaluation morphism are the cokernels of its maps
on stalks. By [lemma-weil-pbc-geometric-stalk-conservative] a
sheaf is zero if and only if all its geometric stalks are zero, so the
cokernel vanishes – that is, the evaluation morphism is an
epimorphism, the defining condition of
[def-kun-global-generated] – exactly when that morphism is
surjective on every geometric stalk.
