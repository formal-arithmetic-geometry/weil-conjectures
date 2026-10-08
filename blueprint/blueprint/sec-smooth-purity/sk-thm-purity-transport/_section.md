+++
id = "sk-thm-purity-transport"
kind = "section"
title = "Smooth purity over $\\mathcal O_E$, $E$ and $\\overline{\\mathbf Q}_\\ell$"
order = 2020
uses = ["sk-def-purity-conv", "sk-lem-sf-flat-model", "sk-prop-a1", "sk-prop-cohsm", "sk-thm-smooth-purity"]
lean = ["AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek"]
+++
*Theorem (sketch).*

Keep the geometric conventions of [sk-def-purity-conv], but let the
coefficient ring range over the remaining three stages

$$
\Lambda\in\{\mathcal O_E,\ E,\ \overline{\mathbf Q}_\ell\},
$$

where $D^b_{ctf}(-,\mathcal O_E)$ is the adic category of normalized
systems $(K_n)_n$ with $K_n\in D^b_{ctf}(-,A_{E,n})$ and common bounds and
stratifications, $D^b_{ctf}(-,E)$ its rationalization, and
$D^b_{ctf}(-,\overline{\mathbf Q}_\ell)$ the colimit over finite
$E/\mathbf Q_\ell$ (Blueprint 01,
`def-weil-pbc-adic-coefficient-datum`,
`def-weil-pbc-rational-category`,
`def-weil-pbc-qbar-category`). Let $f:X\to Y$ be smooth separated
of relative dimension $d$ and let $K\in D^b_{ctf}(Y,\Lambda)$. Then the
purity map

$$
\gamma_{f,K}:Lf^{*}K(d)[2d]\ \xrightarrow{\ \sim\ }\ Rf^{!}K
$$

extends the finite-coefficient isomorphism of [sk-thm-smooth-purity]
to these stages, naturally in $K$ and
compatibly with composition, étale base change, the finite reductions
$A_{E,n}\to A_{E,m}$ and scalar extension of coefficient fields. In
particular, for the structure morphism $a_X$ of a smooth $X$ of pure
dimension $d$,

$$
\omega_{X,\Lambda}=Ra_X^{!}\Lambda\ \cong\ \Lambda_X(d)[2d],
$$

and the counit of $Ra_{X!}\dashv Ra_X^{!}$ is the normalized integration
map $R\Gamma_c(X,\Lambda_X(d)[2d])\to\Lambda$.
The coefficient compatibilities and this counit normalization also hold
for the finite-coefficient isomorphisms of [sk-thm-smooth-purity].
(Blueprint 14,
`thm-pur-finite-reduction-of-purity`,
`thm-pur-adic-reconstruction`,
`thm-pur-rational-and-qbar-purity` and
`cor-pur-adic-and-rational-smooth-dualizing-complexes`.)

## Proof

*Step 1 (compatibility with the finite reductions).* For $m\le n$
write $\mathrm{red}_{n,m}=(-)\otimes^{L}_{A_{E,n}}A_{E,m}$. By
[sk-thm-smooth-purity] the map $\gamma_{f,K}$ is the composite of three
constituents: the canonical twist reassociation, the inverse of the
diagonal identification $\omega_f\cong\Lambda_X(d)[2d]$ of
[sk-thm-smooth-purity], and the tensor formula [sk-prop-cohsm] (b). Each
is compatible with $\mathrm{red}_{n,m}$: the finite-level twist
$A(1)=\mu_{\ell^N}\otimes_{\Z/\ell^N}A$ of [sk-def-purity-conv] and the
Kummer boundary $\kappa(t)$ that orients it ([sk-prop-a1]) reduce to
their counterparts over $A_{E,m}$, and the exceptional adjunction
$Rf_!\dashv Rf^{!}$ is compatible with reduction of the coefficient ring.
Hence $\mathrm{red}_{n,m}(\gamma_{f,K})=\gamma_{f,\mathrm{red}_{n,m}K}$,
and likewise for the orientations, the smooth traces and the composition
and base-change squares of [sk-prop-cohsm] (a),(c).

*Step 2 (the adic stage).* Let
$K\in D^b_{ctf}(Y,\mathcal O_E)$ be the normalized system $(K_n)_n$. By
Step 1 the isomorphisms $\gamma_{f,K_n}$ commute with the transition maps
of the system, so they form a morphism of normalized systems, the common
bounds and stratifications being those of $K$ with the same $d$-shift.
The uniform-tower reconstruction realizes that morphism as a single map
$Lf^{*}K(d)[2d]\to Rf^{!}K$ over $\mathcal O_E$ whose reduction at every
level $n$ is $\gamma_{f,K_n}$; a map of towers that is an isomorphism at
every level is an isomorphism, so $\gamma_{f,K}$ is one.

*Step 3 (the $E$- and $\overline{\mathbf Q}_\ell$-stages).* An
$E$-object is presented by a lattice $K_{\mathcal O_E}$ with
$K_E=K_{\mathcal O_E}\otimes^{L}_{\mathcal O_E}E$. Since
$\mathcal O_E\to E$ is flat, $(-)\otimes^{L}_{\mathcal O_E}E$ is exact and
carries the isomorphism of Step 2 for the lattice to an isomorphism
$\gamma_{f,K_E}$, independently of the chosen lattice because two lattices
agree after inverting $\varpi$. A $\overline{\mathbf Q}_\ell$-object is
represented by an $E$-object for some finite $E/\mathbf Q_\ell$, the
finite-stage categories being idempotent complete, and $\gamma$ transports
along $E\hookrightarrow\overline{\mathbf Q}_\ell$; the transport is well
defined because the purity isomorphisms are transitive in coefficient
extensions and preserve idempotent summands.

*Step 4 (the dualizing complex).* Apply Steps 1–3 to $f=a_X$ and
$K=\Lambda_{\Spec k}$: the purity isomorphism reads
$\omega_{X,\Lambda}\cong\Lambda_X(d)[2d]$, and the counit of
$Ra_{X!}\dashv Ra_X^{!}$ becomes the transported normalized integration
map. Only the finite stage is proved in this document; Steps 2–4 are
sketches of Blueprint 14, where the reconstruction and transport lemmas
are carried out in full.

Uses: [sk-def-purity-conv], [sk-lem-sf-flat-model], [sk-prop-a1], [sk-prop-cohsm], [sk-thm-smooth-purity]
