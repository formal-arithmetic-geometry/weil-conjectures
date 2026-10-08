+++
id = "sk-prop-sf-kunneth-ordinary"
kind = "section"
title = "Künneth and the projection formula in ordinary étale cohomology"
order = 1654
lean = ["AlgebraicGeometry.Etale.nonempty_iso_kunneth"]
+++
*Proposition (sketch).*

Let $k$ be separably closed, $n$ invertible in $k$, and let $X,Y$ be
finite-type $k$-schemes. Then the exterior-product map

$$
\kappa_{E,K}:\RG(X_{\Et},E)\otimes^L_{\Z/n}\RG(Y_{\Et},K)
\longrightarrow\RG\bigl((X\times_kY)_{\Et},p_1^{-1}E\otimes^L_{\Z/n}p_2^{-1}K\bigr)
$$

is an isomorphism for all $E\in D(X_{\Et},\Z/n)$ and $K\in D(Y_{\Et},\Z/n)$
(*unbounded, and with no properness hypothesis*), with the
one-proper-factor forms for complexes with torsion cohomology; and for $f$
proper the projection formula
$Rf_*E\otimes^L\underline K\to Rf_*(E\otimes^Lf^{-1}\underline K)$ is an
isomorphism.
Chapter 16 (Künneth formula in étale cohomology): the general
Künneth theorem is thm:kun-0F1P, its one-proper-factor forms are
lem:kun-0F14a and lem:kun-0F14b, the compact-support form is
its compact-support corollary, and the projection formula is
lem:kun-0F0G (torsion ring) and lem:kun-0F0F (integer
coefficients).

Uses: `def-kun-derived-tensor`, `def-kun-kunneth-map`, `lem-kun-0f0f`, `lem-kun-0f0g`, `lem-kun-0f14a`, `lem-kun-0f14b`, `thm-kun-0f1p`
