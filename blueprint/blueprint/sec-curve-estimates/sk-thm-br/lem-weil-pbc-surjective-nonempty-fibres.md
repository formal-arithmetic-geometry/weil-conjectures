+++
id = "lem-weil-pbc-surjective-nonempty-fibres"
kind = "lemma"
title = "Surjectivity criterion via nonempty geometric fibres"
order = 910
uses = ["def-weil-pbc-scheme-conventions"]
+++
A finite-type morphism whose geometric fibres are all nonempty is surjective.

## Proof

Let $y\in|Y|$ and let $\bar y:\operatorname{Spec}\Omega\to Y$ be a geometric
point over $y$, with $\Omega$ an algebraic closure of $\kappa(y)$. The
geometric fibre $X_{\bar y}$ is nonempty, so some point of $X_{\bar y}$ maps
to a point $x\in X$; under the projection $X_{\bar y}\to X$, the image of
$X_{\bar y}$ maps to the point of $Y$ image of the closed point of
$\operatorname{Spec}\Omega$, namely $y$. Hence $f(x)=y$ for some $x$, so $f$
is surjective on underlying points (the finite-type hypothesis is not needed
for this argument).
