+++
id = "lem-sc-affine-constant-second"
kind = "lemma"
title = "Second cohomology of a constant sheaf on an affine curve"
order = 1013
uses = ["def-sc-curves", "def-weil-pbc-etale-cohomology", "lem-sc-as-sequence", "lem-sc-etale-affine-qcoherent", "lem-sc-pic-affine", "lem-sc-second-kummer-divisors"]
+++
Let $C$ be a smooth affine connected curve
over an algebraically closed field, and $\ell$ any prime.
Then $H^2(C,\mathbf F_\ell)=0$, with
etale cohomology.

## Proof

If $\ell$ is invertible in the field, choosing a primitive
$\ell$-th root identifies $\mathbf F_\ell$ with $\mu_\ell$.
Then [lem-sc-second-kummer-divisors] identifies the group with
$\operatorname{Pic}(C)/\ell=0$, by [lem-sc-pic-affine].
In characteristic $\ell$, use the long exact sequence of
[lem-sc-as-sequence]; the adjacent groups
$H^1(C,\mathbf G_a)$ and $H^2(C,\mathbf G_a)$ vanish by
[lem-sc-etale-affine-qcoherent].
