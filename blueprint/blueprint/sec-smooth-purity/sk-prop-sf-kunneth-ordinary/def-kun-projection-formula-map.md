+++
id = "def-kun-projection-formula-map"
kind = "definition"
title = "The projection-formula morphism"
order = 1735
uses = ["def-kun-derived-tensor", "def-weil-pbc-inverse-image", "lem-kun-inverse-image-monoidal"]
+++
Let $f:X\to Y$ be a morphism of schemes, $\Lambda$ a commutative
ring, $E\in D(X_{\Et},\Lambda)$, and $K\in D(Y_{\Et},\Lambda)$.
The *projection-formula morphism* is the morphism

$$
\mathrm{PF}_f(E,K):\quad
Rf_*E\kunotimes{\Lambda}K\longrightarrow
Rf_*\bigl(E\kunotimes{\Lambda}f^{-1}K\bigr)
$$

in $D(Y_{\Et},\Lambda)$ adjoint to the composite

$$
f^{-1}(Rf_*E\kunotimes{\Lambda}K)
\cong f^{-1}Rf_*E\kunotimes{\Lambda}f^{-1}K
\xrightarrow{\ \varepsilon_f\otimes1\ }E\kunotimes{\Lambda}f^{-1}K,
$$

where the first map is the monoidality isomorphism of
[lem-kun-inverse-image-monoidal] for the
inverse image $f^{-1}$ and
$\varepsilon_f$ is the counit of the derived adjunction.
