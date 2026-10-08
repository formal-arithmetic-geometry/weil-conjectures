+++
id = "lem-wf-schur-scalar"
kind = "lemma"
title = "Schur's scalar lemma"
order = 2539
uses = ["def-wf-simple-module"]
+++
Let a group $A$ act irreducibly on a finite-dimensional vector space
$M$ over the algebraically closed field $\overline{\mathbf Q}_\ell$. If
an endomorphism $c$ commutes with every element of $A$, then
$c=\lambda\,1_M$ for a unique scalar $\lambda$.

## Proof

The operator $c$ has an eigenvalue $\lambda$, since the coefficient
field is algebraically closed. The generalized eigenspace
$\ker(c-\lambda)^{\dim M}$ is nonzero and is stable under $A$, because
$c$ commutes with $A$. Irreducibility makes it all of $M$. Thus
$c-\lambda$ is nilpotent. Its kernel is again a nonzero $A$-stable
subspace, so simplicity as in [def-wf-simple-module] makes it all of
$M$, proving $c=\lambda1_M$.
