+++
id = "sk-def-exchange"
kind = "section"
title = "Exchange morphism"
order = 1035
lean = ["AlgebraicGeometry.Etale.baseChange"]
uses = ["sk-def-conv"]
+++
*Definition (sketch).*

For a cartesian square

$$
\begin{array}{ccc}
X' & \xrightarrow{g'} & X\\
f'\downarrow & & \downarrow f\\
Y' & \xrightarrow{g} & Y
\end{array}
$$

(i.e. $X'=X\times_YY'$) there is a canonical *exchange
morphism*

$$
\Ex_{\square,F}\ :\ g^{-1}Rf_*F\ \longrightarrow\ Rf'_*g'^{-1}F,
$$

namely the adjoint, under $f'^{-1}\dashv Rf'_*$, of the composite

$$
f'^{-1}g^{-1}Rf_*F\ \cong\ g'^{-1}f^{-1}Rf_*F
\xrightarrow{\ g'^{-1}\varepsilon_f\ }g'^{-1}F,
$$

where the isomorphism is induced by $f\circ g'=g\circ f'$ and
$\varepsilon_f$ is the counit of $f^{-1}\dashv Rf_*$; it is natural
in $F$ and independent of all choices.

Uses: [sk-def-conv]
