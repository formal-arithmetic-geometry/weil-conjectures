+++
id = "prop-weil-pbc-strict-henselization-stalk-formula"
kind = "theorem"
title = "Strict-henselization stalk formula"
order = 956
tags = ["latex:proposition"]
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-kinjective-resolutions", "def-weil-pbc-pointed-etale-neighbourhoods", "def-weil-pbc-scheme-conventions", "def-weil-pbc-strict-henselization-limit", "lemma-weil-pbc-affine-neighbourhood-cofinal", "lemma-weil-pbc-etale-cohomology-continuity", "lemma-weil-pbc-fibre-product-limit"]
+++
For quasi-compact quasi-separated $f:X\to S$, torsion $F$, and $q\geq0$,

$$
(R^qf_*F)_{\bar s}\cong
H^q(X\times_SS_{(\bar s)},F|).
$$

For $K\in D^+(X_{\mathrm{et}})$ this lifts to

$$
(Rf_*K)_{\bar s}\xrightarrow{\sim}
R\Gamma(X\times_SS_{(\bar s)},K|)
$$

in $D^+(\mathbf{Ab})$.

## Proof

The stalk is the colimit over $\mathcal N_{\bar s}^{\mathrm{op}}$ of
$H^q(X\times_SV,F|)$. Replace the index by affine neighbourhoods, identify
their inverse limit by Lemma [lemma-weil-pbc-fibre-product-limit], and
apply cohomology continuity. For the derived statement, choose a
bounded-below injective complex $J^\bullet$ representing $K$. The chain map
from the stalk complex $(f_*J^\bullet)_{\bar s}$ to the sections complex on
the strict henselization is obtained by restricting each representative
section. Its map on every cohomology group is the preceding isomorphism, so
it is a quasi-isomorphism. This expands Tag `03Q9`.

## Detailed form

Let $f:X\to S$ be quasi-compact and quasi-separated
[def-weil-pbc-scheme-conventions], let $F$ be a torsion etale sheaf
[def-weil-pbc-etale-sheaves], and let $\bar s\to S$ be geometric. Then

$$
 (R^qf_*F)_{\bar s}\xrightarrow{\sim}
 H^q(X\times_SS_{(\bar s)},F|)
 \qquad(q\geq0),
$$

where $S_{(\bar s)}$ is the strict henselization limit
[def-weil-pbc-strict-henselization-limit] at $\bar s$. For
$K\in\Dplus(X_{\Et})$ with torsion cohomology, this assembles to

$$
 (Rf_*K)_{\bar s}\xrightarrow{\sim}
 \RGamma(X\times_SS_{(\bar s)},K|)
 \quad\text{in }\Dplus(\Ab).
$$

## Proof

The stalk is the colimit over pointed etale neighbourhoods, whose inverse
limit is the strict henselization by
[def-weil-pbc-strict-henselization-limit]; the fibre product
commutation of [lemma-weil-pbc-fibre-product-limit] replaces $X\times_SS_{(\bar
s)}$ by the limit of the $X\times_SV$, and
[lemma-weil-pbc-etale-cohomology-continuity] identifies the colimit of
cohomologies with the cohomology of the limit. On a bounded-below K-injective
[def-weil-pbc-kinjective-resolutions] representative the same argument gives
the derived statement.
