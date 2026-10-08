+++
id = "sk-cor-picard-hilb-sheaf"
kind = "section"
title = "Hilbert functor is the fppf sheaf"
order = 771
uses = ["sk-def-av-jacobian", "sk-thm-picard-descent"]
lean = ["AlgebraicGeometry.isSheaf_hilbertPresheaf"]
+++
*Corollary (sketch).*

By [sk-thm-picard-descent] (D2), $\Hilb^d_{X/S}$ is an fppf (hence
Zariski) sheaf.

## Proof

Let $\{T_i\to T\}_{i\in I}$ be an fppf covering — flat, locally of
finite presentation and surjective, hence fpqc — and let
$Z_i\in\Hilb^d_{X/S}(T_i)$ agree on the double intersections. Base
change gives an fpqc covering $\{X_{T_i}\to X_T\}$ with
$X_{T_i}\times_{X_T}X_{T_{i'}}=X_{T_i\times_TT_{i'}}$, so the closed
immersions $Z_i\hookrightarrow X_{T_i}$ together with that compatibility
form a descent datum. By [sk-thm-picard-descent] (D2) they glue to a
unique closed immersion $Z\hookrightarrow X_T$ with
$Z\times_TT_i\cong Z_i$, and being finite locally free of degree $d$ is
fpqc-local on the target, so $Z\to T$ is finite flat of degree $d$:
$Z\in\Hilb^d_{X/S}(T)$. The uniqueness in (D2) is the injectivity half
of the sheaf condition. Zariski coverings are fppf coverings, whence
also the Zariski sheaf property, which is the form used in
[sk-thm-picard-hilb-general].

This is Stacks, Picard Schemes of Curves, Lemma 44.2.1
([`0B95`](https://stacks.math.columbia.edu/tag/0B95)); the detailed form is Blueprint 50,
`lem-pc-hilb-sheaf`, whose two inputs are descent for closed
immersions ([`03I0`](https://stacks.math.columbia.edu/tag/03I0)) and the fpqc-local nature of
``finite locally free of degree $d$'' ([`02VO`](https://stacks.math.columbia.edu/tag/02VO)).

Uses: [sk-thm-picard-descent]
