+++
id = "sk-thm-dnc"
kind = "section"
title = "DNC invariance of the section dualizing line"
order = 1999
uses = ["sk-def-purity-conv", "sk-lem-geometry", "sk-prop-a1-inv", "sk-prop-an", "sk-prop-cohsm"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone"]
+++
*Theorem (sketch).*

In the situation of [sk-lem-geometry] there is a unique isomorphism

$$
\mathcal C(g,s)\ \xrightarrow{\ \sim\ }\ \mathcal C(\pi_N,0_N)
$$

which, in coordinates carrying $(g,s)$ to $(\Aaf^d_B\to B,0)$, is the
identity on the standard section invariant. It is compatible with étale
localization and arbitrary base change in $B$.

## Proof

*Step 1: the family object is a shift of a lisse line.* By
[sk-lem-geometry] (2) $\widetilde g$ is smooth, so $\omega_{\widetilde g}$ is
invertible by [sk-prop-cohsm] (a), and by [sk-lem-geometry] (2),(4) it is
étale-locally $\Lambda(d)[2d]$; hence so is $\mathcal F$. Truncating a
bounded complex which is étale-locally a shift of a rank-one locally
constant sheaf gives $\mathcal F\simeq\mathcal L_{\mathcal F}(d)[2d]$ with
$\mathcal L_{\mathcal F}$ finite locally constant of rank one on $\Aaf^1_B$,
and likewise $\mathcal C(g,s)\simeq\mathcal L_1(d)[2d]$ on $B$. This
reduction to honest sheaves is what permits the ordinary one-categorical
descent below.

*Step 2: the punctured trivialization.* $\kappa^{\circ}$ of
[sk-lem-geometry] (3) is defined over $\mathbf G_{m,B}$. Let $B_i\to B$ be
an étale cover carrying coordinates of pairs as in [sk-lem-geometry] (2);
on it the standard-pair computation of [sk-lem-geometry] (4) with
[sk-prop-an] supplies
$\kappa_i:\mathcal F|_{\Aaf^1_{B_i}}\xrightarrow{\sim}a_i^{*}\mathcal C(g,s)|_{B_i}$,
normalized to be the identity at $t=1$. Both $j^{*}\kappa_i$ and
$\kappa^{\circ}|_{\mathbf G_{m,B_i}}$ are maps between shifts of lisse
rank-one sheaves agreeing at $t=1$, so they agree on $\mathbf G_{m,B_i}$ by
the second assertion of [sk-prop-a1-inv] (i).

*Step 3: gluing.* On $B_{ij}$ the maps $\kappa_i$ and $\kappa_j$ agree
on $\mathbf G_{m,B_{ij}}$; removing the common shift and twist by Step 1,
the first assertion of [sk-prop-a1-inv] (i) makes them agree on all of
$\Aaf^1_{B_{ij}}$. They therefore glue, by the ordinary sheaf axiom, to a
unique isomorphism $\kappa:\mathcal F\xrightarrow{\sim}a^{*}\mathcal C(g,s)$
extending $\kappa^{\circ}$. Restricting at $t=0$ and using
[sk-lem-geometry] (1) gives the displayed isomorphism; uniqueness is again
[sk-prop-a1-inv] (i). Base change and étale localization are those of
[sk-lem-geometry] (5).

Uses: [sk-def-purity-conv], [sk-lem-geometry], [sk-prop-a1-inv], [sk-prop-an], [sk-prop-cohsm]
