+++
id = "def-weil-extension-by-zero"
kind = "definition"
title = "Extension by zero"
order = 1471
uses = ["def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
Let $A$ be a finite commutative ring, let $U$ and $\overline X$ be schemes,
and let $j:U\hookrightarrow\overline X$ be an open immersion
[def-weil-scheme-morphism-properties] of schemes, and use the small pro-etale
sites [def-weil-pbc-proetale-site]. Use the constant coefficient
sheaf $A$. This includes the rings $A_{E,n}$ of the finite-torsion
coefficient construction [def-weil-finite-torsion-constructibility]. For a
module sheaf $M$ on $U_{\mathrm{proet}}$, define extension by zero by
sheafifying the module presheaf

$$
 P_M(V)=
 \begin{cases}
 M(V\to U),&\text{if }V\to\overline X\text{ factors through }U,\\
 0,&\text{otherwise}.
 \end{cases}
$$

Such a factorization is unique because $j$ is an open immersion. Restriction
is the restriction in $M$ whenever the source factors through $U$, and is the
zero map otherwise. This defines the functor

$$
 j_!: \Sh(U_{\mathrm{proet}},A)
 \longrightarrow \Sh(\overline X_{\mathrm{proet}},A)
$$

by its action on sections and sheafification; no conservativity of ordinary
geometric stalks is part of the definition.
