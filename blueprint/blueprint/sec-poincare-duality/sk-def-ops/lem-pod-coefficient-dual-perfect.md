+++
id = "lem-pod-coefficient-dual-perfect"
kind = "lemma"
title = "Perfectness is preserved by coefficient duality"
order = 2410
uses = ["def-pod-coefficient-dual-on-x", "def-pod-perfect-complex-on-x", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-torsion-constructibility", "lem-pod-finite-projective-tensor-hom", "prop-pod-perfect-local-model"]
+++
In the Poincare duality conventions of
this chapter, let $K\in D^b_{ctf}(X,\Lambda)$ be
perfect over $\Lambda_X$.
Then its coefficient dual
$K^\vee=R\mathcal Hom_X(K,\Lambda_X)$, formed with the
derived internal Hom,
is perfect over $\Lambda_X$ as well, and in particular
$K^\vee\in \hyperref[def-weil-finite-torsion-constructibility]{D^b_{ctf}(X,\Lambda)}$.

## Proof

Being perfect over $\Lambda_X$ is a local condition on the small
pro-etale site of $X$
([def-pod-perfect-complex-on-x]), so it suffices to treat the case
in which $K$ is a bounded complex $P^\bullet$ of finite projective
$\Lambda_X$-modules. For a finite projective $\Lambda_X$-module
$P$ the dual $P^\vee=\mathcal Hom_X(P,\Lambda_X)$ is again finite
projective, being the dual of a direct summand of a finite free module,
and the canonical map $P^\vee\otimes^L_{\Lambda_X}N\to R\mathcal Hom_X(P,N)$ of
[lem-pod-finite-projective-tensor-hom] identifies
$R\mathcal Hom_X(P^\bullet,\Lambda_X)$ with the bounded complex
$(P^\bullet)^\vee$ of finite projective $\Lambda_X$-modules
([def-pod-coefficient-dual-on-x]). Hence $K^\vee$ is perfect
over $\Lambda_X$, and
[prop-pod-perfect-local-model] gives
$K^\vee\in D^b_{ctf}(X,\Lambda)$.
