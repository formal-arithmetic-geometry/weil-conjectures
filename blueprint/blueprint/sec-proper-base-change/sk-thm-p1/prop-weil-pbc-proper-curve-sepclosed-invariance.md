+++
id = "prop-weil-pbc-proper-curve-sepclosed-invariance"
kind = "theorem"
title = "Proper curve invariance over separably closed fields"
order = 1182
tags = ["latex:proposition"]
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-curve-constructible-primary-reduction", "lemma-weil-pbc-curve-dense-open-reduction", "lemma-weil-pbc-curve-locally-constant-reduction", "lemma-weil-pbc-curve-normalization-constant", "lemma-weil-pbc-curve-separably-closed-passage", "lemma-weil-pbc-finite-pushforward-extension-zero", "lemma-weil-pbc-universal-homeomorphism-coverings", "lemma-weil-pbc-universal-homeomorphism-site-equivalence", "prop-weil-pbc-algebraically-closed-extension", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $k\subseteq k'$ be separably closed fields, $C$ a proper $k$-scheme of
dimension at most one, and $F$ a torsion etale sheaf. Then

$$
H^q(C,F)\xrightarrow{\sim}H^q(C_{k'},F|)
$$

for every $q$.

## Proof

First assume both fields algebraically closed. Apply constructible/primary
reduction. The closed immersion $C_{\mathrm{red}}\to C$ is a universal
homeomorphism, so the explicit site equivalence first replaces $C$ by its
reduction. Then apply dense-open localization, the prime-to-$\ell$ trace
splitting, the
finite-pushforward comparison, and the normalized smooth constant calculation
in that order. Every step commutes with field extension, giving the result.
For separably closed $k\subseteq k'$, apply Lemma
[lemma-weil-pbc-curve-separably-closed-passage] to the algebraically
closed result just proved. Its commutative rectangle identifies the
resulting isomorphism with the specified restriction map. This expands Tags
`03SC` and `0A5E`.

## Detailed form

Let $k\subset k'$ be separably closed, let $C$ be proper of dimension at most
one over $k$, and let $F$ be torsion. The same canonical restriction map is an
isomorphism in every degree.

## Proof

Pass to compatible algebraic closures: the isomorphism of
[prop-weil-pbc-algebraically-closed-extension] holds for the two algebraically
closed extensions, and the two purely inseparable extensions identify the
sites by invariance under universal homeomorphisms, so the separably closed
case is obtained by composing the isomorphisms.
