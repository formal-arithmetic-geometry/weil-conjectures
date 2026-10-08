+++
id = "lem-kun-bc-map-on-cohomology"
kind = "lemma"
title = "Cohomology of a derived base-change map"
order = 1752
uses = ["def-kun-truncations", "def-weil-pbc-cartesian-square", "def-weil-pbc-derived-exchange", "def-weil-pbc-direct-image", "def-weil-pbc-underived-exchange"]
+++
For a
cartesian square as in
[def-weil-pbc-cartesian-square] and a sheaf $F$, the morphism on
$q$-th cohomology sheaves induced by

$$
g^{-1}Rf_*F\longrightarrow Rf'_*(g')^{-1}F
$$

is the usual base-change morphism
$g^{-1}R^qf_*F\to R^qf'_*(g')^{-1}F$.

## Proof

The derived exchange morphism is, by
[def-weil-pbc-derived-exchange], the mate of the underived one,
and the mate construction is natural in the object; applying it to the
truncation triangles $\tau_{\le n}$ of
[def-kun-truncations] shows that its $q$-th cohomology sheaf is
the map induced by the underived exchange of the sheaf
$\mathcal H^q(F)$. That induced map is precisely
$g^{-1}R^qf_*F\to R^qf'_*(g')^{-1}F$, by
[def-weil-pbc-underived-exchange] together with the description of
higher direct images in def:weil-pbc-direct-image.
