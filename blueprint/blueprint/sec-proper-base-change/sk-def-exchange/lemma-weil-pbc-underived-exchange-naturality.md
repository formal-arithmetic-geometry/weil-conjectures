+++
id = "lemma-weil-pbc-underived-exchange-naturality"
kind = "lemma"
title = "Sectionwise exchange is natural"
order = 1039
lean = ["AlgebraicGeometry.Etale.baseChangeMap_naturality"]
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-underived-exchange", "lem-weil-pbc-underived-exchange-sectionwise"]
+++
For every morphism $u:F\to G$ the square

$$
\begin{CD}
g^{-1}f_*F @>{\operatorname{Ex}_{\square,F}}>> f'_*g'^{-1}F\\
@V{g^{-1}f_*u}VV @VV{f'_*g'^{-1}u}V\\
g^{-1}f_*G @>{\operatorname{Ex}_{\square,G}}>> f'_*g'^{-1}G
\end{CD}
$$

commutes on every etale object of $Y'$.

## Proof

On a representative section $s_i$ (the sectionwise rule of [lem-weil-pbc-underived-exchange-sectionwise]), both paths first apply $u$ and then
pull back along the same two maps. Since inverse image is a functor, the two
resulting sections of $g'^{-1}G$ are equal on each $V_i$ and therefore after
descent on $V$. Equality for all $V$ is equality of sheaf morphisms.

## Detailed form

For every morphism $a:F\to G$ in $\Ab(X_{\Et})$, the square

$$
 \begin{array}{ccc}
 g^{-1}f_*F&\xrightarrow{\Ex^0_{\square,F}}&f'_*g'^{-1}F\\
 g^{-1}f_*a\downarrow&&\downarrow f'_*g'^{-1}a\\
 g^{-1}f_*G&\xrightarrow{\Ex^0_{\square,G}}&f'_*g'^{-1}G
 \end{array}
$$

commutes.

## Proof

Each arrow in the defining composite of
[def-weil-pbc-underived-exchange] is an adjunction unit, the
specified pseudofunctorial isomorphism $\theta_\square$ of
[def-weil-pbc-cartesian-square], or an adjunction counit; all three
transformations are natural in $F$, so the displayed square commutes.
