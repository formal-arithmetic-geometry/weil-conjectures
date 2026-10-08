+++
id = "thm-sf-fullcd-used-class"
kind = "theorem"
title = "The full cohomological-dimension condition on the blueprint's coefficient class"
order = 1796
uses = ["def-sf-fullcd-used-class", "def-weil-derived-cohomology-sheaves", "def-weil-full-cohomological-dimension", "def-weil-pbc-direct-image", "def-weil-pbc-proetale-site", "def-weil-pbc-site-comparison-morphism", "def-weil-scheme-morphism-properties", "lem-sf-fullcd-detection-equivalence", "lem-sf-proetale-constructible-origin", "thm-sf-fullcd-etale-origin"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, $n\geq1$,
$A=A_{E,n}$, $k=\overline{\mathbf F}_q$, finite-type $k$-schemes $Y$
and $\overline X$ with $\dim\overline X\leq d$
([def-weil-scheme-morphism-properties]) and a proper finite-type
morphism $p:\overline X\to Y$. Then the vanishing required by
[def-weil-full-cohomological-dimension] holds for every coefficient
sheaf of the blueprint's class [def-sf-fullcd-used-class], with the
bound $c=2d$ and uniformly over all base changes $V\to Y$ of
$Y_{\Proet}$; that is,

$$
\mathcal H^r\bigl(R(p_V)_*(\mathcal F|_{\overline X\times_YV})\bigr)=0
\qquad(r>2d)
$$

for every base change $V\to Y$ and every $\mathcal F$ of that class.
Moreover that class is closed under inverse image along morphisms of
finite-type $k$-schemes, under extensions and under colimits, and it
contains the constant coefficient sheaf and every sheaf of étale origin.

## Proof

The vanishing is [thm-sf-fullcd-etale-origin], whose two clauses are
the absolute one and the relative one over every base change and whose bound
is $2\dim\overline X\leq2d$; equivalently, by
[lem-sf-fullcd-detection-equivalence], it is the vanishing of the
pro-étale cohomology of the base-changed source for those coefficients.
The class is stable under inverse image because the comparison pullback
$\nu^*$ of [def-weil-pbc-site-comparison-morphism] is exact and
commutes with the scheme pullbacks of the comparison sites, so the inverse
image of an étale-origin sheaf is étale-origin; it is stable under
extensions and colimits because $\nu^*$, being a left adjoint and exact,
preserves them; and the constructible description of the class is clause (i)
of [lem-sf-proetale-constructible-origin]. The constant coefficient
sheaf is the pullback of the constant étale sheaf, hence lies in the class.
