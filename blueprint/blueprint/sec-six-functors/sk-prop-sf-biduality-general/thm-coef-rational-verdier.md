+++
id = "thm-coef-rational-verdier"
kind = "theorem"
title = "Verdier biduality over a finite coefficient field"
order = 2151
uses = ["def-weil-rationalization-karoubi", "lem-coef-integral-finite-extension", "lem-coef-integral-residue-tor", "prop-weil-pbc-rational-transport", "thm-coef-integral-verdier"]
+++
For every finite extension $E/\Ql$, integral duality induces
an exact $E$-linear anti-equivalence

$$
D_{X,E}:D^b_c(X,E)^{\mathrm{op}}\xrightarrow{\sim}D^b_c(X,E).
$$

Its evaluation and natural isomorphism
$\delta_K:K\xrightarrow{\sim}D_{X,E}D_{X,E}K$ are obtained
by rationalizing integral evaluation and biduality. The dualizing
object is the image $\omega_{X,E}$ of $\omega_{X,\mathcal O_E}$.
For $E\subset L$, the canonical comparison

$$
(D_{X,E}K)\otimes_E L\xrightarrow{\sim}
D_{X,L}(K\otimes_E L)
$$

commutes with evaluation and $\delta$, and satisfies the unit
and associator equations for scalar extension.

## Proof

Put $\mathcal C=D^b_c(X,\mathcal O_E)$. Its actual objects,
not merely a separately chosen finite-Tor subcategory, are in the
domain of integral duality by [lem-coef-integral-residue-tor].
The exact functor $D_{X,\mathcal O_E}:\mathcal C^{\mathrm{op}} \to\mathcal C$ of [thm-coef-integral-verdier] is
$\mathcal O_E$-linear. Apply
[prop-weil-pbc-rational-transport] to the opposite category
as well as to $\mathcal C$. More explicitly, it sends

$$
f/\varpi_E^r:K\longrightarrow M
\quad\hbox{to}\quad
D(f)/\varpi_E^r:D(M)\longrightarrow D(K).
$$

The equality relation on fractions and their compositions is
preserved by linearity and contravariant functoriality. Thus this
is a functor on exactly the raw scalar localization
[def-weil-rationalization-karoubi]; there is no extra
idempotent completion or assumption about the choice of a lattice.

The integral natural transformation $\delta$ and its inverse
localize. Its naturality for fractions follows by multiplying
the integral naturality equation by the same scalar denominator.
Consequently $D_{X,E}^2\cong\operatorname{id}$, proving the
anti-equivalence. Evaluation and its transpose localize as well.
Finally localize all the comparisons and their equations in
[lem-coef-integral-finite-extension]. The scalar-extension
functor used there is exactly the one on integral representatives
in [def-weil-rationalization-karoubi], so the resulting
comparison has the asserted domain and coherence.
