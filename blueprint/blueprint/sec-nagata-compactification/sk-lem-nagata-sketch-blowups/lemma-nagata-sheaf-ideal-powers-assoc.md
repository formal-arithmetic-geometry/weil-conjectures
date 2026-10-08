+++
id = "lemma-nagata-sheaf-ideal-powers-assoc"
kind = "lemma"
title = "Associativity of ideal-power multiplication"
order = 104
+++
**Status.** Bypassed by the formalized route: no separate relative-Proj
primitive was formalized. The blow-up is glued from the affine Proj charts
(`AlgebraicGeometry.Proj.basicOpenIsoSpec`,
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`) with
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`.

For a quasi-coherent ideal $\mathcal I\subseteq\mathcal O_X$, the canonical
maps $\mathcal I^m\otimes\mathcal I^n\to\mathcal I^{m+n}$ are associative
and have $\mathcal I^0=\mathcal O_X$ as a two-sided unit.

## Proof

On an affine open $\operatorname{Spec}(A)$ these maps are induced by
multiplication of the ideals $I^m$ and $I^n$ in $A$. Associativity and the
unit law are therefore the corresponding ring identities. Localization
preserves these identities, and equality of morphisms of quasi-coherent
sheaves can be checked on an affine cover, so the identities glue on $X$.
