+++
id = "lem-weil-pbc-standard-quotients-perfect"
kind = "lemma"
title = "Perfectness of the standard quotients"
order = 1254
uses = ["def-weil-pbc-adic-coefficient-datum"]
+++
For $A=\Zl$ and $I=(\ell)$, the quotient $P_n=\mathbf Z/\ell^n\mathbf Z$ is
perfect over $\Zl$, represented by

$$
 [\Zl\xrightarrow{\ell^n}\Zl]
$$

in degrees $-1$ and $0$, in the sense of
[def-weil-pbc-adic-coefficient-datum]. The analogous two-term resolution
holds for $\mathcal O_E/\varpi^n$ over the ring of integers $\mathcal O_E$ of
a finite extension $E/\Ql$.

(*Source note:* perfectness is that of Stacks Project, More on Algebra,
Definition 15.76.1 (Tag
[0657](https://stacks.math.columbia.edu/tag/0657)): an object of $D(R)$ is
perfect if it is quasi-isomorphic to a bounded complex of finite projective
$R$-modules, so the displayed two-term complex of finite free $A$-modules
presents $P_n$ as a perfect complex. Stacks states the definition for a ring
$R$; the form used here is the same notion for $A=\Zl$ and $A=\mathcal O_E$
with $P_n=A/I^n$, and [def-weil-pbc-adic-coefficient-datum] additionally
requires each $P_n$ to be finite as a set.)

## Proof

A uniformizer is a non-zero-divisor in a complete discrete valuation ring, so
the displayed two-term complex is a finite free resolution of the quotient,
which is therefore perfect as required by
[def-weil-pbc-adic-coefficient-datum].
