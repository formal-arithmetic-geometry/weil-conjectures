+++
id = "lem-kun-proj-formula-natural"
kind = "lemma"
title = "Naturality of the projection formula"
order = 1753
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-inverse-image", "lem-kun-inverse-image-monoidal"]
+++
Consider a
cartesian square as in
[def-weil-pbc-cartesian-square]. Let $\Lambda$ be a ring,
$E\in D(X_{\Et},\Lambda)$, and $K\in D(Y_{\Et},\Lambda)$. The
following square commutes:

$$
\begin{array}{ccc}
g^{-1}(Rf_*E\kunotimes{\Lambda}K)
&\xrightarrow{\;g^{-1}\mathrm{PF}_f\;}&
g^{-1}Rf_*(E\kunotimes{\Lambda}f^{-1}K)\\
\Big\downarrow{\scriptstyle \Ex\otimes1}&&
\Big\downarrow{\scriptstyle \Ex}\\
Rf'_*(g')^{-1}E\kunotimes{\Lambda}g^{-1}K
&\xrightarrow{\;\mathrm{PF}_{f'}\;}&
Rf'_*\bigl((g')^{-1}E\kunotimes{\Lambda}(f')^{-1}g^{-1}K\bigr).
\end{array}
$$

Here the canonical monoidal identifications for inverse image are
understood. Thus, whenever the displayed exchange and
projection-formula morphisms are isomorphisms, their inverses satisfy the same compatibility.

## Proof

Both composites are the mates of the same composite built from the
unit–counit pair of
[def-weil-pbc-inverse-image], the monoidality of the inverse
images [lem-kun-inverse-image-monoidal], and the
$\theta$-identification: the left
vertical map is $\Ex$ of the $E$-factor, and the two projections
formula maps are the mates of $\varepsilon_f\otimes1$ (resp. $\varepsilon_{f'}\otimes1$); the compatibility of $\theta$ with
the identifications of the pulled-back square makes the two routes
equal, hence the diagram commutes by the injectivity of the
adjunction bijection.
