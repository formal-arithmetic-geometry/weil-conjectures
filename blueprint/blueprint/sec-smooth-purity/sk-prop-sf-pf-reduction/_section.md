+++
id = "sk-prop-sf-pf-reduction"
kind = "section"
title = "Projection formula: compatibility with finite reduction"
order = 1880
uses = ["sk-def-sf-exchanges", "sk-lem-sf-determination", "sk-thm-sf-pf-finite"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek", "AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_leftDerivedUpperStar"]
+++
*Proposition (sketch).*

Let $m\le n$ and let $K\in\Dctf(X,A_{E,n})$, $L\in\Dctf(Y,A_{E,n})$ with
reductions $K_m,L_m$. Then the square comparing
$\operatorname{PF}_{f,K,L}$ and $\operatorname{PF}_{f,K_m,L_m}$ through the
finite-reduction compatibilities of $Rf_!$, $-\otimes^L$ and $Lf^*$ commutes;
hence $\operatorname{PF}_{f,K,L}$ is an isomorphism if and only if
$\operatorname{PF}_{f,K_m,L_m}$ is.

## Proof

Write $\rho=-\otimes^L_{A_{E,n}}A_{E,m}$ for finite reduction on every
scheme; it commutes strictly with $Lf^*$ and $j_!$ and is compatible with
$\otimes^L$ through the monoidal structure of scalar extension,
$\rho(M\otimes^LN)\cong\rho M\otimes^L\rho N$. Recall how the maps in the
square are constructed. With $f=\bar f\circ j$ a compactification,
$\operatorname{PF}_{f,K,L}$ is ([sk-def-sf-exchanges]) the identification
$j_!K\otimes^L\bar f^*L\cong j_!(K\otimes^Lf^*L)$ composed with the
direct-image projection map for $\bar f$, which is *defined* as the
transpose under $L\bar f^*\dashv R\bar f_*$ of the *counit–tensor map*
$L\bar f^*(R\bar f_*M\otimes^LL)\cong L\bar f^*R\bar f_*M\otimes^LL\bar f^*L \xrightarrow{\ \varepsilon\otimes1\ }M\otimes^LL\bar f^*L$. The
finite-reduction comparison for $R\bar f_*$ (hence for $Rf_!$) is likewise
*defined* as the adjunction mate of the pullback comparison
$\rho L\bar f^*=L\bar f^*\rho$:
$\rho R\bar f_*M\to R\bar f_*L\bar f^*\rho R\bar f_*M=R\bar f_*\rho L\bar f^* R\bar f_*M\xrightarrow{R\bar f_*\rho\varepsilon}R\bar f_*\rho M$. Now
transpose both routes around the square under $L\bar f^*\dashv R\bar f_*$.
Each becomes a map $L\bar f^*\rho(R\bar f_*M\otimes^LL)\to\rho M\otimes^L L\bar f^*\rho L$ which moves $\rho$ past $L\bar f^*$ and $\otimes^L$ by the
comparisons above and applies the counit; the route through
$\operatorname{PF}_{f,K,L}$ applies $\varepsilon$ to $M$ and then reduces,
the route through $\operatorname{PF}_{f,K_m,L_m}$ reduces and then applies
$\varepsilon$ to $\rho M$. These agree: by the definition of the
$R\bar f_*$-comparison as a mate, the counit of the reduced adjunction is the
reduction of the counit, and the tensor comparisons are coherent
(associativity and unit of the monoidal structure of $\rho$). Hence the two
transposes coincide, and the square commutes as a square of the specified
maps. This is an equality of morphisms proved from the constructions; it is
*not* inferred from agreement at $P=A_{E,n}$ or at geometric stalks,
which would be insufficient ([sk-lem-sf-determination]). Both horizontal
maps are isomorphisms by [sk-thm-sf-pf-finite], whence the equivalence of
invertibility.

Uses: `\Cref{thm-sf-pf-finite}`, `prop-functor-package`, [sk-def-sf-exchanges], [sk-lem-sf-determination]
