+++
id = "thm-weil-pbc-universal-homeomorphism-invariance"
kind = "theorem"
title = "Universal-homeomorphism invariance"
order = 999
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "def-weil-pbc-inverse-image", "def-weil-pbc-kinjective-resolutions", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-universal-homeomorphism-base-change", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
If $u:X'\to X$ is a universal homeomorphism
[def-weil-pbc-scheme-conventions], then the morphisms of small etale sites
[def-weil-pbc-etale-site] induced by $u$ give an equivalence of small etale
topoi, i.e. an equivalence of the categories of etale sheaves

$$
 \operatorname{Sh}(X_{\Et})\xrightarrow{\ \sim\ }\operatorname{Sh}(X'_{\Et}),
$$

compatible with the inverse and direct image functors and with cohomology.
The equivalence preserves and reflects covering families and is compatible
with identities, composition, and pullback of sheaves and cohomology.

## Proof

The input is the topological invariance of the small etale site
[def-weil-pbc-etale-site]: for a universal homeomorphism
[def-weil-pbc-scheme-conventions] $u:X'\to X$, base change $V\mapsto
V\times_XX'$ is an equivalence of the small etale categories, naturally in
the schemes and compatible with identities and composites, and it preserves
and reflects jointly surjective families, because the underlying topological
map of $u$ and of every base change of $u$ is a homeomorphism (Stacks
Project, Section 59.45, Tag
[04DY](https://stacks.math.columbia.edu/tag/04DY), Theorem
[04DZ](https://stacks.math.columbia.edu/tag/04DZ)). The inverse functors of
the equivalence are the inverse image $u^{-1}$ and the direct image $u_*$ of
[def-weil-pbc-inverse-image]: the equivalence of sites makes $u^{-1}$ exact
and $u_*$ its quasi-inverse, so the categories of
[def-weil-pbc-etale-sheaves] are equivalent,

$$
 \operatorname{Sh}(X_{\Et})\xrightarrow{\ \sim\ }
 \operatorname{Sh}(X'_{\Et}),
$$

and covering families are preserved and reflected by the site-equivalence
input. For the compatibility with cohomology, let $F\to I$ be a resolution by
a bounded-below complex of injective sheaves (K-injective by
[prop-weil-pbc-kinjective-resolutions-exist], so the model of
[def-weil-pbc-kinjective-resolutions] computes $H^q(X_{\Et},F)$). Exactness
of $u^{-1}$ sends the resolution to a resolution of $u^{-1}F$ with injective
entries: for an injective $I^m$ the right adjoint criterion applied to the
adjunction of [def-weil-pbc-inverse-image] gives that
$\operatorname{Hom}(u^{-1}I^m,-)\cong\operatorname{Hom}(I^m,u_*-)$ is exact.
The unit and counit of [def-weil-pbc-inverse-image] are the isomorphisms of
the equivalence, so
$\Gamma(X',u^{-1}I)=\Gamma(X,u_*u^{-1}I)=\Gamma(X,I)$ and hence

$$
 H^q(X_{\Et},F)\xrightarrow{\sim}H^q(X'_{\Et},u^{-1}F)
 \qquad(q\geq0),
$$

the compatibilities with identities, composition, and pullback of sheaves
being the functoriality of the site equivalence: the equivalence of a
composite is the composite of the equivalences, and for a base change $u'$ of
$u$ — itself a universal homeomorphism by
[lem-weil-pbc-universal-homeomorphism-base-change] — the equivalences of $u$
and $u'$ form a commutative square with the inverse-image functors of
[def-weil-pbc-inverse-image], which is the compatibility with pullback.
