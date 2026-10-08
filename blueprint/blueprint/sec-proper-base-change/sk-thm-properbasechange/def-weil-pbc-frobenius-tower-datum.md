+++
id = "def-weil-pbc-frobenius-tower-datum"
kind = "definition"
title = "Frobenius-equivariant square and Weil tower"
order = 1332
uses = ["def-weil-pbc-level-map-arrows", "def-weil-pbc-level-map-corners"]
+++
A Frobenius-equivariant datum for the proper Cartesian square $\square$ and
the tower $K_\bullet$ includes displayed witnesses

$$
\epsilon_X^{-1}L_n\xrightarrow{\sim}K_n,
\qquad L_n\in D_c^+(X_{\mathrm{et}},P_n),
$$

compatible with the tower transitions. Pullback supplies the corresponding
etale-origin witnesses for $E_n=L(g')^*K_n$. The datum then consists of
automorphisms

$$
\operatorname{Fr}_X,\quad \operatorname{Fr}_Y,\quad
\operatorname{Fr}_{X'},\quad \operatorname{Fr}_{Y'}
$$

such that

$$
\begin{aligned}
f\operatorname{Fr}_X&=\operatorname{Fr}_Yf,&
g\operatorname{Fr}_{Y'}&=\operatorname{Fr}_Yg,\\
g'\operatorname{Fr}_{X'}&=\operatorname{Fr}_Xg',&
f'\operatorname{Fr}_{X'}&=\operatorname{Fr}_{Y'}f'.
\end{aligned}
$$

The four resulting Frobenius faces are equipped with their Cartesian
identifications, and these identifications make the resulting cube commute
with the chosen Cartesian identification for $\square$. Put
$\Phi_Z=L\operatorname{Fr}_Z^*$. Since every $\operatorname{Fr}_Z$ is an
automorphism, every $\Phi_Z$ is an exact equivalence and preserves products
and fibres.

The pullback faces give canonical isomorphisms

$$
\kappa_g:\Phi_{Y'}Lg^*\xrightarrow{\sim}Lg^*\Phi_Y,
\qquad
\kappa_{g'}:\Phi_{X'}L(g')^*\xrightarrow{\sim}L(g')^*\Phi_X.
$$

The proper Frobenius faces give finite-level exchange isomorphisms

$$
\beta_{f,n}:\Phi_YRf_*K_n\xrightarrow{\sim}Rf_*\Phi_XK_n,
\qquad
\beta_{f',M}:\Phi_{Y'}Rf'_*M\xrightarrow{\sim}Rf'_*\Phi_{X'}M.
$$

Finally the datum contains isomorphisms

$$
\vartheta_n:\Phi_XK_n\xrightarrow{\sim}K_n
$$

such that, for $r_{n+1,n}:K_{n+1}\to K_n$,

$$
r_{n+1,n}\vartheta_{n+1}
=\vartheta_n\Phi_X(r_{n+1,n}).
$$

The constant coefficient quotients carry their identity Frobenius
structures, and all displayed comparisons are required to respect their
normalizations and cocycles.
