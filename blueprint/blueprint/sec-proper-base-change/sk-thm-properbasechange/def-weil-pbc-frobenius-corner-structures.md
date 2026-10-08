+++
id = "def-weil-pbc-frobenius-corner-structures"
kind = "definition"
title = "Weil structures on the four finite corners"
order = 1333
uses = ["def-weil-pbc-frobenius-tower-datum"]
+++
For $E_n=L(g')^*K_n$, define

$$
\vartheta_{E,n}:=
L(g')^*(\vartheta_n)\,\kappa_{g',K_n}:
\Phi_{X'}E_n\xrightarrow{\sim}E_n.
$$

The Weil structures on $B_n$ and $D_n$ are the typed composites

$$
\begin{aligned}
\Theta_{B,n}:\Phi_{Y'}B_n
&\xrightarrow{\kappa_g}Lg^*\Phi_YRf_*K_n
\xrightarrow{Lg^*\beta_{f,n}}Lg^*Rf_*\Phi_XK_n
\xrightarrow{Lg^*Rf_*\vartheta_n}B_n,\\
\Theta_{D,n}:\Phi_{Y'}D_n
&\xrightarrow{\beta_{f',E_n}}Rf'_*\Phi_{X'}E_n
\xrightarrow{Rf'_*\vartheta_{E,n}}D_n.
\end{aligned}
$$

Transport these structures across the two projection-formula isomorphisms:

$$
\Theta_{A,n}:=h_n^{-1}\Theta_{B,n}\Phi_{Y'}(h_n),
\qquad
\Theta_{C,n}:=(h'_n)^{-1}\Theta_{D,n}\Phi_{Y'}(h'_n).
$$

Thus every $\Theta_{Z,n}$ has the genuine Weil type
$\Phi_{Y'}Z_n\xrightarrow{\sim}Z_n$ for
$Z=A,B,C,D$.
