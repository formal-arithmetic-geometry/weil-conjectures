+++
id = "prop-weil-pbc-p1-strict-henselian-comparison"
kind = "theorem"
title = "Strictly henselian $\\mathbf P^1$ comparison"
order = 1142
tags = ["latex:proposition"]
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-kinjective-resolutions", "def-weil-pbc-strict-henselian-setup", "lemma-weil-pbc-etale-degree-zero", "lemma-weil-pbc-p1-injective-acyclic", "prop-weil-pbc-p1-acyclicity"]
+++
For every torsion sheaf $F$ on $X$, restriction induces isomorphisms

$$
H^q(X,F)\xrightarrow{\sim}H^q(X_0,F_0)\qquad(q\geq0).
$$

## Proof

Choose an injective resolution $F\to I^\bullet$. Exactness of inverse
image along the closed immersion gives an exact complex $F_0\to I_0^\bullet$.
The preceding lemma makes each $I_0^r$ acyclic, so Leray's acyclicity lemma
identifies $R\Gamma(X_0,F_0)$ with $\Gamma(X_0,I_0^\bullet)$. Degree-zero
restriction identifies this complex with $\Gamma(X,I^\bullet)$ term by term.
Taking cohomology gives the displayed isomorphisms, and naturality follows
from the naturality of the restriction map and of injective resolutions. The
source locators are Tags `0A0C` and `0A3S`.

## Detailed form

In the setup of [def-weil-pbc-strict-henselian-setup], for every torsion
etale sheaf $F$ on $X$, restriction gives natural isomorphisms

$$
 H^q(X,F)\xrightarrow{\sim}H^q(X_0,F_0)
 \qquad(q\geq0).
$$

## Proof

Choose a K-injective resolution $F\to I^\bullet$. By the acyclicity statement
of [prop-weil-pbc-p1-acyclicity] each $I^m|_{X_0}$ is acyclic on $X_0$, so
$H^q(X_0,F_0)$ is computed by $\Gamma(X_0,I^\bullet|_{X_0})$; the degree-zero
comparison, applied termwise to the abelian sheaves $I^m$, identifies this
with $\Gamma(X,I^\bullet)$, whose cohomology is $H^q(X,F)$. Naturality in $F$
is the naturality of the two comparisons in the setup of
[def-weil-pbc-strict-henselian-setup].
