+++
id = "thm-sf-biduality-class"
kind = "theorem"
title = "Verdier biduality on the coefficient class"
order = 2156
uses = ["lem-coef-integral-residue-tor", "lem-weil-verdier-preservation-strata", "thm-coef-integral-verdier", "thm-coef-qbar-verdier", "thm-coef-rational-verdier", "thm-fix-general-biduality"]
+++
Let $X$ be separated of finite type over $\Fbar$, and let
$\Lambda=A_{E,n},\mathcal O_E,E$, or $\Qlb$.
Use the constructible coefficient categories of the blueprint and put
$\omega_{X,\Lambda}=Ra_X^!\Lambda$,
$D_{X,\Lambda}=R\mathcal Hom_\Lambda(-,\omega_{X,\Lambda})$.
Then $D_{X,\Lambda}$ is an exact contravariant anti-equivalence
of $D^b_{ctf}(X,\Lambda)$, and the evaluation-defined map

$$
K\longrightarrow D_{X,\Lambda}D_{X,\Lambda}K
$$

is a natural isomorphism. At the integral and field stages this is
the whole specified category $D^b_c(X,\Lambda)$.

At finite coefficients, an input Tor interval $[a,b]$ gives
$[-b-2\dim X,-a]$ for its dual. At integral coefficients the
same assertion holds for the uniform Tor intervals of the finite
reductions. In particular the finite or integral dualizing object
has interval $[-2\dim X,0]$. Field objects may be computed from
any integral representative and then localized.

## Proof

The finite-stage anti-equivalence is [thm-fix-general-biduality],
with its independent bound from
[lem-weil-verdier-preservation-strata]. The normalized-tower
argument and the integral evaluation comparison give
[thm-coef-integral-verdier], including the same reduction bounds.
Its domain is the whole integral constructible category by
[lem-coef-integral-residue-tor].
The exact scalar localization and the common finite coefficient
stage give respectively [thm-coef-rational-verdier] and
[thm-coef-qbar-verdier]. Those proofs transport the evaluation
map itself, so the resulting isomorphism is the stated double-dual
map at every coefficient stage.
