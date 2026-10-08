+++
id = "thm-sf-fullcd-class"
kind = "theorem"
title = "The blueprint's coefficient class supplies the restricted datum, with $c=2\\dim\\overline X$"
order = 1800
uses = ["def-sf-fullcd-class", "def-sf-fullcd-used-class", "def-weil-full-cohomological-dimension", "def-weil-pbc-site-comparison-morphism", "def-weil-scheme-morphism-properties", "lem-sf-fullcd-class-restriction", "lem-sf-proetale-constructible-origin", "prop-sf-comparison-bound-zero", "thm-sf-fullcd-etale-origin", "thm-sf-fullcd-used-class", "thm-sp-grothendieck"]
+++
In the setting of [thm-sf-fullcd-used-class] — $k=\Fbar$,
finite-type $k$-schemes $Y$ and $\overline X$ with
$\dim\overline X\leq d$, and a
proper finite-type morphism
$p:\overline X\to Y$ — the class-restricted datum of
[def-sf-fullcd-class] holds for $p$ with the bound $2d$:

$$
\operatorname{FullCD}_{\mathrm{cls}}(p,A;2d).
$$

The bound is $2\dim\overline X\leq2d$ and it is uniform over all base
changes $V\to Y$ of $Y_{\Proet}$; the comparison bound on the class is
moreover the sharp $M=0$ of [prop-sf-comparison-bound-zero], so that
the residual $2\dim\overline X$ is the étale direction of the Leray
spectral sequence of [thm-sp-grothendieck] and not a lower bound on
$R^q\nu_{\overline X,*}$.

## Proof

The two clauses of [def-sf-fullcd-class] are the two clauses of
[def-weil-full-cohomological-dimension] read on the blueprint's
coefficient class, and [thm-sf-fullcd-used-class] is exactly their
assertion with the coefficient sheaves of that class. Indeed the class
quantified over in that theorem is
[def-sf-fullcd-used-class], which is by its definition the class of
étale origin on the finite-type source $\overline X$, the same class that
[def-sf-fullcd-class] quantifies over; the identification of that class
with the constructible one, used only for reading the statement, is
[lem-sf-proetale-constructible-origin]. The absolute clause is
therefore the first clause of [thm-sf-fullcd-used-class], whose bound
$2\dim\overline X$ is the one of [thm-sf-fullcd-etale-origin]. The
relative clause is the second clause of [thm-sf-fullcd-used-class],
which asserts the vanishing of the base-changed direct images for every base
change $V\to Y$ and every coefficient sheaf of the class; the restriction
of such a sheaf to the base-changed source is again a coefficient sheaf of
the class there, by [lem-sf-fullcd-class-restriction], so the two
statements quantify over the same base-changed coefficients, and the second
clause of [def-sf-fullcd-class] is exactly that relative clause. The
last sentence of the statement is [prop-sf-comparison-bound-zero], the
residual $2\dim\overline X$ being the étale direction of the Leray
spectral sequence of [thm-sp-grothendieck]; the comparison morphism
that appears there is the one of
[def-weil-pbc-site-comparison-morphism].
