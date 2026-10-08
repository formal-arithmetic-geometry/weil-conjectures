+++
id = "def-weil-finite-torsion-constructibility"
kind = "definition"
title = "Finite-torsion constructibility"
order = 1454
uses = ["def-weil-derived-cohomology-sheaves", "def-weil-finite-field-fiber", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
For the global finite-field datum [def-weil-finite-field-fiber], fix a prime
$\ell\neq p$, a finite extension $E/\Ql$, a uniformizer $\varpi_E$ of its
valuation ring $\mathcal O_E$, an integer $n\in\mathbf Z_{\geq1}$, and a
scheme $Y$. On the small pro-etale site
[def-weil-pbc-proetale-site] $Y_{\mathrm{proet}}$, put

$$
  A_{E,n}=\mathcal O_E/\varpi_E^n.
$$

A sheaf of $A_{E,n}$-modules on $Y_{\mathrm{proet}}$ is *constructible* if
there is a finite disjoint partition $Y=\bigsqcup_{\nu=1}^N Y_\nu$ by locally
closed constructible subschemes [def-weil-scheme-morphism-properties], and
the restriction to each $Y_\nu$ is locally constant with finite
$A_{E,n}$-module stalks. For a derived complex, for every $i\in\mathbf Z$,
write $\mathcal H^i$ for its cohomology sheaves
[def-weil-derived-cohomology-sheaves]. Define

$$
 D^b_c(Y,A_{E,n})\subset D(Y_{\mathrm{proet}},A_{E,n})
$$

to be the full triangulated subcategory of complexes with finitely many
nonzero cohomology sheaves, all constructible.
