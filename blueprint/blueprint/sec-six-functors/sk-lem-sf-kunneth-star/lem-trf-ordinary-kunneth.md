+++
id = "lem-trf-ordinary-kunneth"
kind = "lemma"
title = "Ordinary Kunneth for a general morphism"
order = 2218
uses = ["def-trf-coefficient-conventions", "def-weil-finite-tor-amplitude", "def-weil-scheme-morphism-properties", "lem-kun-0f1j", "lem-kun-0f1n", "lem-sf-flat-model"]
+++
Use the finite coefficient ring $A=A_{E,n}$ of
[def-trf-coefficient-conventions]. Let $f:X\to Y$ be a morphism of
separated finite-type
schemes, let $Z$ be an auxiliary such scheme, and let $L\in D^b_{ctf}(X,A)$, $Q\in D^b_{ctf}(Z,A)$ in the
finite-Tor constructible
category. Then the canonical comparison

$$
Rf_*L\boxtimes_A^{\mathrm L} Q
\xrightarrow{\ \sim\ }
R(f\times\operatorname{id}_Z)_*\bigl(L\boxtimes_A^{\mathrm L} Q\bigr)
$$

is an isomorphism, natural in $L$ and $Q$.

## Proof

Consider the Cartesian square

$$
\begin{gathered}
X\times Z \xrightarrow{f\times\operatorname{id}_Z} Y\times Z,\\
p_X:X\times Z\to X,\qquad p_Y:Y\times Z\to Y,\qquad
p_Z:X\times Z\to Z,\qquad p'_Z:Y\times Z\to Z,
\end{gathered}
$$

with $p_Z=p'_Z\circ(f\times\operatorname{id}_Z)$. Writing the external
product as
$L\boxtimes_A^{\mathrm L}Q=p_X^*L\otimes_A^{\mathrm L}p_Z^*Q =p_X^*L\otimes_A^{\mathrm L}(f\times\operatorname{id}_Z)^*\bigl(p'_Z{}^*Q\bigr)$,
the canonical comparison is the composite

$$
\begin{aligned}
Rf_*L\boxtimes_A^{\mathrm L}Q
= p_Y^*Rf_*L\otimes_A^{\mathrm L}p'_Z{}^*Q
&\longrightarrow
R(f\times\operatorname{id}_Z)_*\bigl(p_X^*L\bigr)
\otimes_A^{\mathrm L}p'_Z{}^*Q\\
&\longrightarrow
R(f\times\operatorname{id}_Z)_*\bigl(L\boxtimes_A^{\mathrm L}Q\bigr)
\end{aligned}
$$

of the base-change map along $p_Y$ and the projection map for the ordinary
direct image $R(f\times\operatorname{id}_Z)_*$. Neither map is an isomorphism
by a general theorem: $Z$ is an arbitrary finite-type scheme, so $p_Y$ is
smooth only when $Z$ is and smooth base change does not apply, and the
projection formula for $Rf_*$ (as opposed to $Rf_!$) is not an isomorphism in
general.

*Step 1: $\mathbf Z/N$-coefficients.* Put $N=\ell^n$, so that $A$ is a
$\mathbf Z/N$-algebra. With $K=k$, $X\leftarrow X'\leftarrow Y$ and
$\Spec K\leftarrow S'\leftarrow T$ of [lem-kun-0f1n] taken to be
$Z\leftarrow Z\times Y\leftarrow Z\times X$ and
$\Spec k\leftarrow Y\xleftarrow{f}X$, that lemma says precisely that for
every $E\in D(Z_{\Et},\mathbf Z/N)$ and $F\in D(X_{\Et},\mathbf Z/N)$ the
canonical map

$$
p'_Z{}^{*}E\otimes^{\mathrm L}_{\mathbf Z/N}p_Y^*Rf_*F
\longrightarrow
R(f\times\operatorname{id}_Z)_*\bigl(p_Z^*E\otimes^{\mathrm L}_{\mathbf Z/N}p_X^*F\bigr)
$$

is an isomorphism (its bounded form is [lem-kun-0f1j]). This is the
assertion for $\mathbf Z/N$-coefficients, up to the symmetry of the tensor
product.

*Step 2: coefficient transport to $A$.* Let $P$ be the bounded flat
$A$-model of $L$ given by [lem-sf-flat-model]. Both sides of the
comparison are exact in $Q$, so the finite $\varpi_E$-adic filtration
$Q\supseteq\varpi_EQ\supseteq\dots$ of a bounded complex (equivalently, the
triangles $\varpi_E^{i+1}\mathcal H^q\to\varpi_E^{i}\mathcal H^q\to
\varpi_E^{i}\mathcal H^q/\varpi_E^{i+1}\mathcal H^q$ on the cohomology
sheaves, together with the truncation triangles) reduces the assertion to
the case where $Q$ is a single sheaf of $\kappa$-modules,
$\kappa=A/(\varpi_E)$. For such $Q$,
$P\otimes_A Q=(P\otimes_A\kappa)\otimes_\kappa Q$ with $P\otimes_A\kappa$ a
complex of flat $\kappa$-module sheaves, and the comparison for
$(L,Q)$ over $A$ is the comparison for $(P\otimes_A\kappa,Q)$ over the
finite field $\kappa$. Step 1 and the proof of [lem-kun-0f1j] are linear
over the coefficient field — truncations, flat resolutions, filtered colimits
of constructible sheaves, the embedding of a constructible sheaf into a
finite sum of $\pi_{i*}$ of constant sheaves for finite $\pi_i$, and dimension
shifting — and apply verbatim with the finite field $\kappa$ in place of
$\mathbf F_\ell$; alternatively, $\kappa$ is a finite free
$\mathbf F_\ell$-module, so $\kappa$-linear constructible sheaves are
$\mathbf F_\ell$-constructible sheaves with a $\kappa$-action and the
$\kappa$-linear comparison is a direct summand of the $\mathbf F_\ell$-linear
one.

The composite is the canonical comparison, since both maps are natural in
their variables; naturality in $L$ and $Q$ follows from the functoriality of
the base-change and projection maps.
(*Provenance:* Stacks Project, Étale Cohomology, Lemma 59.97.8,
[Tag `0F1N`](https://stacks.math.columbia.edu/tag/0F1N), which is
[lem-kun-0f1n] here, together with SGA 5, III, 1.1 and 1.6.4 for the
coefficient and site generality used here.)
