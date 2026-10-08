+++
id = "lem-pur-kunneth-supported"
kind = "lemma"
title = "Kunneth for cohomology with closed support"
order = 1939
uses = ["def-kun-derived-tensor", "def-kun-tor-amplitude", "def-pur-support-cohomology", "def-pur-supported-exterior-product", "def-weil-finite-field-fiber", "def-weil-pbc-derived-categories", "def-weil-pbc-etale-origin-witness", "def-weil-scheme-morphism-properties", "lem-kun-kunneth-map-natural", "lem-pur-ordinary-kunneth-finite-ring", "lem-pur-support-restriction-triangle", "lem-weil-pbc-comparison-pullback", "prop-weil-pbc-comparison-direct-image", "thm-weil-pbc-site-comparison"]
+++
Let $k$ be the algebraically closed field of
[def-weil-finite-field-fiber], put
$A=\mathcal O_E/\varpi_E^n$, and let $Z\subset X,W\subset Y$
be closed subschemes of
separated finite-type
$k$-schemes.
Let $K\in D^b(X_{\mathrm{et}},A)$ and
$L\in D^b(Y_{\mathrm{et}},A)$ be
bounded complexes,
with $L$ of
finite Tor amplitude.
Then the supported
exterior product is an isomorphism:

$$
\kappa^{Z,W}_{K,L}:
R\Gamma_Z(X,K)\otimes_A^LR\Gamma_W(Y,L)
\xrightarrow{\ \sim\ }
R\Gamma_{Z\times W}(X\times_kY,K\boxtimes_A^L L).
$$

Here $R\Gamma_Z,R\Gamma_W$ are the
derived support functors.
The assertion also holds for the pro-etale realizations of these
complexes equipped with
etale-origin witnesses.

## Proof

Put $U=X\setminus Z$, $V=Y\setminus W$ and
$F=K\boxtimes_A^L L$.
Finite Tor amplitude makes $F$ and its restrictions bounded below.
Apply [lem-pur-support-restriction-triangle] on $Y$ with
$B=Y,C=W$, and tensor its triangle with $R\Gamma(X,K)$.
Compare it with the support triangle on $X\times Y$ for
$X\times W$. The ordinary Kunneth maps on $X\times Y$ and
$X\times V$ are isomorphisms by
[lem-pur-ordinary-kunneth-finite-ring].
They commute with restriction because both maps pull back and
tensor the two sections ([lem-kun-kunneth-map-natural]). The induced map of the first terms is
therefore an isomorphism:

$$
R\Gamma(X,K)\otimes_A^LR\Gamma_W(Y,L)
\xrightarrow{\sim}R\Gamma_{X\times W}(X\times Y,F).
$$

The same argument with $U$ in place of $X$ gives

$$
R\Gamma(U,K|_U)\otimes_A^LR\Gamma_W(Y,L)
\xrightarrow{\sim}R\Gamma_{U\times W}(U\times Y,F|_{U\times Y}).
$$

Next apply [lem-pur-support-restriction-triangle] with
$T=X\times Y$, $B=X\times W$, $C=Z\times Y$, and
open complement $U\times Y$.
Compare this triangle with the support triangle for $Z\subset X$
tensored with $R\Gamma_W(Y,L)$.
The second and third terms are identified by the preceding two
isomorphisms. Exactness of derived tensor from
[def-kun-derived-tensor] and the long exact cohomology
sequences show that the first-term map is an isomorphism.
On the injective support-resolution model, this map sends the
tensor of two supported sections to their exterior product; hence
it is the map of [def-pur-supported-exterior-product].
This also proves its naturality and compatibility with restriction.

For the pro-etale assertion, the exact comparison functor in
[thm-weil-pbc-site-comparison] commutes with pullback by
[lem-weil-pbc-comparison-pullback].
It also preserves derived sections and the open direct images by
[prop-weil-pbc-comparison-direct-image].
Consequently the ordinary localization triangles
$R\Gamma_Z(X,K)\to R\Gamma(X,K)\to R\Gamma(U,K|_U)$
and their product diagrams identify the etale and pro-etale
support objects for the specified witnesses.
Tensor and the two counits are transported as well, so the
resulting supported exterior-product map is the pro-etale map.
Transporting the proved isomorphism establishes the assertion.
