+++
id = "lem-weil-pbc-proetale-restriction-injectives"
kind = "lemma"
title = "Pro-etale localization preserves injectives"
order = 1280
uses = ["def-weil-pbc-etale-sum-extension", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-operations", "def-weil-pbc-proetale-site", "lem-weil-pbc-ind-etale-stability", "prop-weil-pbc-proetale-constant-exact"]
+++
For a weakly etale $v:W\to X$, the site $W_{\Proet}$ is the slice of
$X_{\Proet}$ over $W$. The restriction functor on constant-coefficient module
sheaves is exact and preserves injectives. Consequently derived evaluation on
$W$, computed in sheaves on $X_{\Proet}$, agrees with derived global sections
on $W_{\Proet}$.

## Proof

Composition and base change preserve weak etaleness by the stability lemma
for ind-etale algebras. A morphism between two weakly etale $X$-schemes is
weakly etale as well. On rings, factor $B\to C$ as $B\to B\otimes_AC\to C$.
The first arrow is weakly etale by base change; the second is a base change
of the flat diagonal of $B/A$. This second map is a flat ring epimorphism,
whose own diagonal is an isomorphism, so is weakly etale. The scheme
assertion follows on affine opens. Objects, morphisms, and coverings of the
small pro-etale site therefore identify the slice with $W_{\Proet}$.

The construction of extension by zero along an etale map applies on this
slice with exactly the same formula: sheafify

$$
 V\longmapsto\bigoplus_{s:V\to W\text{ over }X}M(V,s).
$$

A map from this presheaf to $N$ is precisely a family of maps $M(V,s)\to
N(V)$ compatible with restrictions, hence a map to the restriction of $N$.
This proves its left adjunction to restriction. The constructed functor is
exact. Kernels are computed summand by summand before sheafification, which
is exact for module presheaves. For an epimorphism of sheaves on the slice, a
local section of the displayed direct sum has finite support. Lift its
finitely many summands on coverings in the slice and take a common covering
of $V$. Thus its sheafification is locally surjective and hence an
epimorphism. This proves exactness without a claim about ordinary geometric
stalks on the pro-etale site.

The adjunction now makes restriction preserve injectives. Restriction itself
is exact by the exactness of the pro-etale inverse image for constant
coefficients; it is the inverse image of the pro-etale operations for this
localization. Restricting an injective resolution therefore computes both
versions of derived sections in the statement.
