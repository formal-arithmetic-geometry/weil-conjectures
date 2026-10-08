+++
id = "sk-lem-sf-mate"
kind = "section"
title = "Mate calculus for a pasted adjunction"
order = 1869
uses = ["sk-def-sf-admissible", "sk-def-sf-operations", "sk-prop-sf-comparison", "sk-prop-sf-existence", "sk-thm-sf-comp-composition"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp"]
+++
*Lemma (sketch).*

Let $X\xrightarrow{f}Y\xrightarrow{g}Z$ be composable separated finite-type
morphisms of finite-type $k$-schemes.

- **(a)** *Ambient form (conditional; optional).* Assume that $f$, $g$
and $gf$ carry the ambient exceptional right adjoint datum of
[sk-def-sf-admissible] (1), so that the ambient adjunctions
$Rf_!\dashv Rf^{\times}$, $Rg_!\dashv Rg^{\times}$ and
$R(gf)_!\dashv R(gf)^{\times}$ of [sk-def-sf-operations] (v) are given.
Then the mate of the composition isomorphism
$R(gf)_!\cong Rg_!Rf_!$ of [sk-thm-sf-comp-composition] under these
adjunctions is an isomorphism of ambient functors
$R(gf)^{\times}\cong Rf^{\times}Rg^{\times}:D(Z,\Lambda)\to D(X,\Lambda)$, and
the unit and counit of $Rg_!Rf_!\dashv Rf^{\times}Rg^{\times}$ are the pasted
ones; under the mate they are the unit and counit of
$R(gf)_!\dashv R(gf)^{\times}$. (The datum is not available in general,
[sk-rem-sf-fullcd-scope]; this clause is used nowhere below.)
- **(b)** *Restricted form (unconditional).* For the constructible
exceptional adjoints $Rf^!$, $Rg^!$, $R(gf)^!$ of [sk-def-sf-operations] (vi)
— the functors $\nu^*f^{\times}R\nu_*$ of [sk-prop-sf-existence] (c),
which exist for every separated finite-type $f$, $g$ — the mate of
$R(gf)_!\cong Rg_!Rf_!$ on the bounded-below complexes of étale origin,
under the adjunctions of [sk-prop-sf-existence] (c), is an isomorphism
$(gf)^!\cong f^!g^!:D^+(Z,\Lambda)\to D^+(X,\Lambda)$, the units and
counits of the composite adjunctions being the pasted ones; it restricts to
$\Dctf(Z,\Lambda)\to\Dctf(X,\Lambda)$ as soon as the three functors are known
to preserve $\Dctf$ ([sk-prop-sf-rf-shriek-preservation], whose proof uses
only the $D^+$-form of this clause, so there is no circularity). No
admissibility datum is assumed; when the ambient datum of (a) happens to
hold, (b) is the restriction of (a).

The notation $(gf)^!\cong f^!g^!$ used below always refers to (b).

## Proof

(a) The pasting is recorded in fix-prop-adjunctions; the functoriality of
the mate construction gives an isomorphism of right adjoints from the
isomorphism of left adjoints, and the triangle identities of the composite
are the composites of the component ones. Nothing here uses constructibility
or finite Tor amplitude: the statement is formal in the ambient adjunctions,
which are exactly what clause (1) supplies. (b) On the étale sites the adjunctions of
[sk-prop-sf-existence] (a) are honest adjunctions on the whole of $D(-_{\Et},A)$,
so the formal mate calculus of (a) applies verbatim and gives
$(gf)^{\times}\cong f^{\times}g^{\times}$ with pasted units and counits;
$(gf)^!\cong f^!g^!$ is its transport along $\nu^*$, using
$Rf_{!}\nu^*\cong\nu^*Rf^{\Et}_!$ ([sk-prop-sf-comparison]) and the full
faithfulness of $\nu^*$ on $D^+$, which identifies the adjunction isomorphisms
of [sk-prop-sf-existence] (c) with the étale ones. The restriction to
$\Dctf$ is then immediate from the preservation.

Uses: `\Cref{sk-def-sf-operations}`, `\Cref{thm-sf-comp-composition}`, `fix-prop-adjunctions`, [sk-def-sf-admissible]
