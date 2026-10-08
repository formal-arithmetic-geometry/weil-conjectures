+++
id = "sk-lem-sf-kunneth-star"
kind = "section"
title = "Ordinary Künneth with an identity factor"
order = 2217
uses = ["sk-lem-sf-flat-model", "sk-prop-sf-comparison", "sk-prop-sf-kunneth-ordinary"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar"]
+++
*Lemma (sketch).*

Let $f:X\to Y$ be a morphism of separated finite-type $k$-schemes, let $Z$ be
a further such scheme, and let $L\in\Dctf(X,\Lambda)$,
$Q\in\Dctf(Z,\Lambda)$. Then the canonical comparison

$$
Rf_*L\boxtimes Q\ \xrightarrow{\ \sim\ }\
R(f\times\operatorname{id}_Z)_*\bigl(L\boxtimes Q\bigr)
$$

is an isomorphism, natural in $L$ and $Q$.

## Proof

Write $p_X:X\times Z\to X$, $p_Z:X\times Z\to Z$ and $p_Y:Y\times Z\to Y$,
$p_Z':Y\times Z\to Z$ for the projections, so that
$p_Z=p_Z'\circ(f\times\operatorname{id}_Z)$ and the square with vertical maps
$f\times\operatorname{id}_Z$ and $f$ is Cartesian. The canonical comparison
is the composite of the base-change map
$p_Y^*Rf_*L\to R(f\times\operatorname{id}_Z)_*p_X^*L$ and the projection map
$R(f\times\operatorname{id}_Z)_*(p_X^*L)\otimes^L_\Lambda p_Z'^*Q\to R(f\times\operatorname{id}_Z)_*(L\boxtimes Q)$, where
$L\boxtimes Q=p_X^*L\otimes^L_\Lambda(f\times\operatorname{id}_Z)^*p_Z'^*Q$.
Neither factor is an instance of a general theorem of this blueprint: $Z$ is
an arbitrary finite-type $k$-scheme, so the projection $p_Y$ is smooth only
when $Z$ is, and smooth base change does not apply; and the projection
formula for the ordinary direct image $Rf_*$ is not an isomorphism in general
(the compact-support formula of [sk-rem-sf-pf-done] concerns $Rf_!$). The
statement is instead the ordinary external-product theorem with one
morphism, [0F1N](https://stacks.math.columbia.edu/tag/0F1N)
([lem-kun-0f1n], with its bounded form
[0F1J](https://stacks.math.columbia.edu/tag/0F1J), [lem-kun-0f1j]), valid for
arbitrary finite-type schemes over a field in which $N$ is invertible and for
arbitrary $\mathbf Z/N$-complexes, and it belongs to the same circle as the
Künneth theorem [sk-prop-sf-kunneth-ordinary]
([0F1P](https://stacks.math.columbia.edu/tag/0F1P)), which supplies its
geometric input: truncations and flat resolutions reduce $L$ to a flat
module sheaf and $Q$ to a single constructible sheaf, which embeds into a
finite sum of $\pi_{i*}$ of constant sheaves for finite morphisms $\pi_i$;
both sides commute with the exact functors
$(\operatorname{id}\times\pi_i)_*$, so dimension shifting in the
cohomological degree reduces to constant $Q$, i.e. to the base change
$p_Y^*Rf_*L\cong R(f\times\operatorname{id}_Z)_*p_X^*L$ along the projection
from a product over the separably closed $k$, which is where the Künneth
theorem enters. *Coefficient transport.* 0F1N is stated for
$\mathbf Z/N$-modules; at the finite stage $\Lambda=A_{E,n}$ the bounded flat
$A$-model of $L$ ([sk-lem-sf-flat-model]) and the $\varpi_E$-adic filtration
of the cohomology sheaves of $Q$ reduce the assertion, both sides being exact
in $Q$ and $-\otimes_A^LQ$ being underived on a flat model, to coefficients in
the finite field $\kappa=A/(\varpi_E)$, with $L$ a complex of flat
$\kappa$-module sheaves; the argument of 0F1J is linear over its
coefficient field and applies verbatim with $\kappa$ in place of
$\mathbf F_\ell$. Both steps are natural in $L$ and $Q$, so the isomorphism
is the canonical comparison; [sk-prop-sf-comparison] transports it to the
pro-étale site. The same statement is SGA 5, III, 1.1 and 1.6.4.

Uses: `\Cref{sk-prop-sf-kunneth-ordinary}`, `\Cref{sk-lem-sf-flat-model}`, `\Cref{sk-prop-sf-comparison}`, `lem-kun-0f1n`, `lem-kun-0f1j`
