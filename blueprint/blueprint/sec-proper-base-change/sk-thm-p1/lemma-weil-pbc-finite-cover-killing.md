+++
id = "lemma-weil-pbc-finite-cover-killing"
kind = "lemma"
title = "Finite-cover killing and finite pushforward monicity"
order = 1127
uses = ["lemma-weil-pbc-finite-stage-killing", "lemma-weil-pbc-finite-stalk-formula"]
+++
For a fixed $c\in H^q(T_0,C_0)$ with $q>0$ and constructible $C$, there is a
finite finitely presented cover $h:V\to T$ whose closed-fibre pullback
$h_0^*c$ is zero; the induced map $C\hookrightarrow h_*h^*C$ is monic.

## Proof

Use the integral strictly-local cover killing $c$ and represent it by the
filtered system of finite, finitely presented covers
$h_\lambda:V_\lambda\to T$. Lemma [lemma-weil-pbc-finite-stage-killing]
selects an index $\lambda_0$ at which $h_{\lambda_0,0}^*c=0$; set
$h=h_{\lambda_0}$. The map to the finite pushforward is the unit of
$(h^*,h_*)$. At a geometric point its stalk is the diagonal into the finite
product of stalks from Lemma [lemma-weil-pbc-finite-stalk-formula]; the
factor corresponding to the chosen point above it is the identity. Hence the
unit is injective on every geometric stalk and therefore monic.
