+++
id = "sbc-thm-e-coefficient-smooth-base-change"
kind = "theorem"
title = "$E$-coefficient smooth base change"
order = 1445
uses = ["def-weil-pbc-rational-category", "sbc-def-admissible-lattices", "sbc-def-base-change-square", "sbc-thm-adic-smooth-base-change", "sbc-thm-smooth-base-change"]
+++
In the square of
[sbc-thm-smooth-base-change], assume $f$ smooth, $g$ quasi-compact
and quasi-separated, all schemes noetherian, $\ell$ invertible, and let
$K_E\in\Dbc(T,E)$ admit a finite-level etale admissible lattice. Then
the exchange morphism is an isomorphism in the ambient rationalized
complete category

$$
Lf^*_{\mathrm{comp},E}Rg_{*,\mathrm{comp},E}K_E
\xrightarrow{\ \sim\ }Rh_{*,\mathrm{comp},E}Le^*_{\mathrm{comp},E}K_E
\quad\text{in }D_{\mathrm{comp}}(S,E),
$$

independent of the lattice, and an isomorphism in $\Dbc(S,E)$ if the
lattice is square-constructibly admissible.

## Proof

The two-term free resolution
$[\mathcal O_E\xrightarrow{\varpi^{n+1}}\mathcal O_E]$ of $A_n$ and
the adic theorem [sbc-thm-adic-smooth-base-change] give the
statement for integral lattices; central localization (inverting
multiplication by $\varpi$) of
[def-weil-pbc-rational-category] gives
it for $K_E$, independent of the admissible lattice, and the
constructible landing is the four-system hypothesis of
[sbc-def-admissible-lattices].
