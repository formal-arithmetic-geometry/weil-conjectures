+++
id = "thm-pur-dnc-invariance"
kind = "theorem"
title = "DNC invariance of the section dualizing line"
order = 2002
uses = ["def-pur-conventions", "def-pur-dnc-section-family", "def-weil-scheme-morphism-properties", "lem-pur-dnc-section-geometry", "lem-pur-lisse-rank-one-aut", "prop-pur-dnc-family-constancy"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting), in the situation of
[def-pur-dnc-section-family], there is a unique isomorphism

$$
C(g,s)\;\xrightarrow{\ \sim\ }\;C(\pi_N,0_N)
$$

which, in coordinates carrying $(g,s)$ to
$(\mathbf A^d_B\to B,0)$, is the identity on the standard section
invariant. It is compatible with etale localization and arbitrary base
change in $B$.

## Proof

Write $a:\mathbf A^1_B\to B$, let
$i_0,i_1:B\rightrightarrows\mathbf A^1_B$ be the sections $t=0$ and
$t=1$, and let $\kappa:F\xrightarrow{\sim}a^*C(g,s)$ be the
canonical isomorphism of
[prop-pur-dnc-family-constancy](2). By
[lem-pur-dnc-section-geometry](1) the fibre of $\widetilde g$
over $t=0$ is the normal bundle $\pi_N:N_s\to B$ with its zero
section, and $i_0^*F\simeq C(\pi_N,0_N)$; hence the inverse of
$i_0^*\kappa$ is a canonical isomorphism
$C(g,s)\to C(\pi_N,0_N)$. In coordinates carrying $(g,s)$ to
$(\mathbf A^d_B\to B,0)$ it is the identity on the standard section
invariant, because there the deformation is the pulled-back standard
family and $\kappa$ restricts to the pullback identification (Step 3
of the proof of [prop-pur-dnc-family-constancy]). It is unique:
two such isomorphisms differ by a locally constant unit on $B$ by
[lem-pur-lisse-rank-one-aut](1)–(2), and that unit is trivial on
every coordinate chart $B_i$, hence trivial on $B$.
Compatibility with etale localization and base change is
[prop-pur-dnc-family-constancy](4).
