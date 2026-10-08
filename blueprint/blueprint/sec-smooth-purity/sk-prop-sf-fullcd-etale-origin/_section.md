+++
id = "sk-prop-sf-fullcd-etale-origin"
kind = "section"
title = "$\\operatorname{FullCD}$ on the étale-origin class"
order = 1787
uses = ["sk-def-sf-admissible", "sk-prop-sf-comparison", "sk-prop-sf-finiteness"]
lean = ["AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar"]
+++
*Proposition (sketch).*

Let $k$ be separably closed, let $p:\overline X\to Y$ be a proper morphism of
finite-type $k$-schemes and let $A=A_{E,n}$ be a finite coefficient stage.
Then for every étale $A$-module sheaf $\mathcal F$ on $\overline X_{\Et}$,

$$
\mathcal H^r\bigl(Rp_{\Proet,*}\,\nu_{\overline X}^*\mathcal F\bigr)=0
\qquad(r>2\dim\overline X),
$$

and the same bound holds for the base change $p_V$ along every object
$V\to Y$ of $Y_{\Proet}$. Equivalently,
$\operatorname{FullCD}(p,A;2\dim\overline X)$ of [sk-def-sf-admissible]
holds on the essential image of $\nu_{\overline X}^*$ — which by
09AK contains every bounded constructible pro-étale $A$-complex,
hence all of $\Dctf(\overline X,A)$.

## Proof

The ring $A=A_{E,n}$ is finite, so every étale sheaf of $A$-modules is
torsion and the torsion bound applies to all of them; this is the quantifier
of the present statement, over the étale-origin class, and *not* the
quantifier of [sk-def-sf-admissible] (1) over every pro-étale sheaf of
$A$-modules, which fails ([sk-rem-sf-fullcd-scope]). Since $k$ is separably
closed, $\mathrm{cd}_{\mathrm{tor}}(k)=0$, so
$\mathrm{cd}_{\mathrm{tor}}(\overline X)\le2\dim\overline X$ by
[sk-prop-sf-finiteness]; properness gives $R^rp_{\Et,*}\mathcal F=0$ for
$r>2\dim\overline X$. The comparison [sk-prop-sf-comparison] identifies
$Rp_{\Proet,*}\nu_{\overline X}^*$ with $\nu_Y^*Rp_{\Et,*}$ for the
quasi-compact quasi-separated $p$, and $\nu_Y^*$ is exact, so the vanishing
transports. The bound depends only on $\dim\overline X$, which the base
changes in question do not increase, so it is uniform in $V$.

Uses: `\Cref{sk-def-sf-admissible}`, `\Cref{sk-prop-sf-comparison}`, `\Cref{sk-prop-sf-finiteness}`
