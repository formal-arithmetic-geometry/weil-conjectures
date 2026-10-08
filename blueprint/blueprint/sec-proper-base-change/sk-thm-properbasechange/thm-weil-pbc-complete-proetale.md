+++
id = "thm-weil-pbc-complete-proetale"
kind = "theorem"
title = "Complete pro-etale proper base change"
order = 1349
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-completed-base-change-map", "def-weil-pbc-completed-pullback", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-levelwise-isomorphism-cones", "lemma-weil-pbc-completed-exchange-coherence", "lemma-weil-pbc-completed-map-reduction", "prop-weil-pbc-direct-image-limits", "thm-weil-pbc-finite-level-proetale"]
+++
Let $A$ and $I$ satisfy the adic coefficient datum, let $f:X\to Y$ be
proper, and let $g:Y'\to Y$ be arbitrary. Suppose $K\in D(X_{\Proet},A)$ is
derived $I$-complete and, for every $n$, $K_n$ is equipped with an
etale-origin witness [def-weil-pbc-etale-origin-witness]
$$
 L_n\in\Dplus(X_{\Et},P_n),
 \qquad \nu_X^*L_n\xrightarrow{\sim}K_n,
$$
compatible with transition maps. Then
$$
 \Ex^{\mathrm{comp}}_{\square,K}:
 Lg^*_{\mathrm{comp}}Rf_*K
 \xrightarrow{\sim}Rf'_*Lg'^*_{\mathrm{comp}}K
$$
is an isomorphism.

*Source note:* for proper base change on the pro-etale site, see Stacks
Project, Pro-etale Cohomology, Section 61.30
([Tag 09C8](https://stacks.math.columbia.edu/tag/09C8)). This statement is
Theorem 61.30.1 there
([Tag 09C9](https://stacks.math.columbia.edu/tag/09C9)): for $f:X\to Y$
proper, a Noetherian ring $\Lambda$ with an ideal $I$ such that $\Lambda/I$
is torsion, and $K\in D(X_{\Proet})$ derived complete with
$K\otimes^L_\Lambda\underline{\Lambda/I^n}$ bounded below with cohomology
sheaves coming from $X_{\Et}$ and $\Lambda/I^n$ a perfect $\Lambda$-module,
the base change map $Lg^*_{comp}Rf_*K\to Rf'_*L(g')^*_{comp}K$ is an
isomorphism. Hypothesis comparison: the blueprint's etale-origin witness is
exactly Stacks' condition that $K\otimes^L_\Lambda\underline{\Lambda/I^n}$
be bounded below and of etale origin, and the perfectness of $P_n=A/I^n$ is
required in the adic coefficient datum; what the blueprint adds is the
tower-level form, in which the witnesses are required to be compatible over
$n$ and the completed pullback is the one defined in
[def-weil-pbc-completed-pullback] from Lemma 61.20.2 ([Tag
099N](https://stacks.math.columbia.edu/tag/099N)), the proof running through
the finite-level rectangle and the completed-map reduction rather than
through Stacks' reduction to etale cohomology.

## Proof

By the finite-level theorem [thm-weil-pbc-finite-level-proetale], each
finite-level exchange map $\Ex_{\square,K_n}$ is an isomorphism. By
[lemma-weil-pbc-completed-map-reduction], the evaluations of the tower
morphism $V'$ are exactly these isomorphisms, so the levelwise-isomorphism
criterion for cones makes $V'$, and hence the composite defining
$\Ex^{\mathrm{comp}}_{\square,K}$ in
[def-weil-pbc-completed-base-change-map], an isomorphism; the
direct-image/limit commutation used there is the direct-image-limits
proposition. Naturality and coherence are
[lemma-weil-pbc-completed-exchange-coherence].
