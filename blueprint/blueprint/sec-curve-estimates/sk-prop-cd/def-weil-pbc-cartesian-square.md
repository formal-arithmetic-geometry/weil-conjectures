+++
id = "def-weil-pbc-cartesian-square"
kind = "definition"
title = "Cartesian square and chosen pullback identification"
order = 994
lean = ["AlgebraicGeometry.Etale.squareUpperStarIso"]
uses = ["def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions"]
+++
For schemes and morphisms

$$
\begin{CD}
X' @>{g'}>> X\\
@V{f'}VV       @VV{f}V\\
Y' @>{g}>> Y,
\end{CD}
$$

we write $\square=(f,f',g,g',\alpha)$ when
$\alpha:X'\xrightarrow{\sim}X\times_Y Y'$ is a specified isomorphism and
$f\circ g'=g\circ f'$ as maps to $Y$. The notation
$g'^{-1}F$ always means inverse image using this specified identification.

## Detailed form

A *cartesian square* $\square=(f,f',g,g',\alpha)$ is a diagram

$$
 \begin{array}{ccc}
 X'&\xrightarrow{g'}&X\\
 f'\downarrow&&\downarrow f\\
 Y'&\xrightarrow{g}&Y
 \end{array}
$$

of scheme morphisms [def-weil-pbc-scheme-conventions] together with a chosen
identification $\alpha:X'\xrightarrow{\sim}X\times_YY'$ and the corresponding
equality $fg'=gf'$. This choice gives a specified natural isomorphism

$$
 \theta_\square:f'^{-1}g^{-1}\xrightarrow{\sim}g'^{-1}f^{-1}
$$

of inverse image [def-weil-pbc-inverse-image] functors, compatible with
identities and pasted squares.
