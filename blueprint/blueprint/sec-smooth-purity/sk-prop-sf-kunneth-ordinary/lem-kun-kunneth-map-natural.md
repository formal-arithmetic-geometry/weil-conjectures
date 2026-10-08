+++
id = "lem-kun-kunneth-map-natural"
kind = "lemma"
title = "Naturality of the Kunneth map"
order = 1741
uses = ["def-kun-kunneth-map", "def-weil-pbc-cartesian-square", "def-weil-pbc-inverse-image"]
+++
Let

$$
\begin{array}{ccc}
X\times_SY&\xrightarrow{\;q\;}&Y\\
\Big\downarrow{\scriptstyle p}&&\Big\downarrow{\scriptstyle g}\\
X&\xrightarrow{\;f\;}&S
\end{array}
$$

be a cartesian square, $\Lambda$ a commutative ring, and let
$E\to E'$ and $K\to K'$ be morphisms in
$D(X_{\Et},\Lambda)$, respectively $D(Y_{\Et},\Lambda)$. Then the
square

$$
\begin{array}{ccc}
Rf_*E\kunotimes{\Lambda}Rg_*K&\xrightarrow{\ \kappa_{E,K}\ }&
Rc_*\bigl(p^{-1}E\kunotimes{\Lambda}q^{-1}K\bigr)\\
\Big\downarrow{\scriptstyle Rf_*(\varphi)\otimes Rg_*(\psi)}&&
\Big\downarrow{\scriptstyle Rc_*(p^{-1}\varphi\otimes q^{-1}\psi)}\\
Rf_*E'\kunotimes{\Lambda}Rg_*K'&\xrightarrow{\ \kappa_{E',K'}\ }&
Rc_*\bigl(p^{-1}E'\kunotimes{\Lambda}q^{-1}K'\bigr)
\end{array}
$$

commutes; that is, $\kappa$ is natural in $E$ and in $K$.

## Proof

By [def-kun-kunneth-map] the map $\kappa_{E,K}$ is the mate,
under the fixed adjunction $c^{-1}\dashv Rc_*$ of
[def-weil-pbc-inverse-image], of a composite whose constituents
are the fixed identification $c^{-1}\cong p^{-1}f^{-1}\cong q^{-1}g^{-1}$, the monoidal comparison, and the counits
$\varepsilon_f$, $\varepsilon_g$; every constituent is natural in
$E$ and $K$. The mate of a composite natural in these variables
under a fixed adjunction is natural, hence the displayed square
commutes.
