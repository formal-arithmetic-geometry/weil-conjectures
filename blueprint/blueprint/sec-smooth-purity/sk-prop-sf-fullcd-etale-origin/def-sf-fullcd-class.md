+++
id = "def-sf-fullcd-class"
kind = "definition"
title = "The class-restricted full cohomological-dimension datum"
order = 1799
uses = ["def-sf-fullcd-used-class", "def-weil-derived-cohomology-sheaves", "def-weil-derived-direct-image", "def-weil-finite-torsion-constructibility", "def-weil-full-cohomological-dimension", "def-weil-pbc-etale-sheaves", "def-weil-pbc-proetale-site", "def-weil-pbc-site-comparison-morphism", "def-weil-scheme-morphism-properties", "lem-sf-fullcd-class-restriction", "lem-sf-proetale-constructible-origin"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, an integer
$n\geq1$, $A=A_{E,n}$ with the
finite-torsion
coefficient convention, $k=\Fbar$, finite-type $k$-schemes $Y$ and
$\overline X$, and a proper
finite-type $k$-morphism $p:\overline X\to Y$. Use the
small pro-étale sites, the
derived direct image $Rp_*$, and
the cohomology-sheaf
functor $\mathcal H^r$. Call a sheaf $\mathcal F$ of $A$-modules on
$\overline X_{\Proet}$ a *coefficient sheaf of the blueprint's class*
if it is of étale origin,
$\mathcal F\cong\nu_{\overline X}^*\mathcal G$ for a sheaf $\mathcal G$
of $A$-modules on $\overline X_{\Et}$ in the sense of
[def-weil-pbc-etale-sheaves], the comparison morphism
$\nu_{\overline X}$ being that of
[def-weil-pbc-site-comparison-morphism]; this is the class of
[def-sf-fullcd-used-class], read on the source $\overline X$, and by
[lem-sf-proetale-constructible-origin] it is also the class of
constructible pro-étale coefficient sheaves. For an integer
$c\in\mathbf Z_{\geq0}$, write
$\operatorname{FullCD}_{\mathrm{cls}}(p,A;c)$ if

$$
\mathcal H^r(Rp_*\mathcal F)=0\qquad(r\in\mathbf Z,\ r>c)
$$

for every coefficient sheaf $\mathcal F$ of that class on
$\overline X_{\Proet}$, and if, for every object $V\to Y$ of
$Y_{\Proet}$ and every such $\mathcal F$, the base change
$p_V:\overline X\times_YV\to V$ of $p$ satisfies

$$
\mathcal H^r\bigl(R(p_V)_*(\mathcal F|_{\overline X\times_YV})\bigr)=0
\qquad(r\in\mathbf Z,\ r>c),
$$

the restriction $\mathcal F|_{\overline X\times_YV}$ being the pullback
along the projection $\overline X\times_YV\to\overline X$, which is again
of étale origin on the base-changed source by
[lem-sf-fullcd-class-restriction]. The two displayed clauses are the
two clauses of [def-weil-full-cohomological-dimension] with the
quantifier over *all* sheaves of $A$-modules replaced by the
quantifier over this class, and nothing else is changed: in particular
$\operatorname{FullCD}(p,A;c)$ implies
$\operatorname{FullCD}_{\mathrm{cls}}(p,A;c)$ for every $c$, the class
being a class of sheaves. The class-restricted datum is the form
the blueprint uses, and it is the form referred to as the class form below.
