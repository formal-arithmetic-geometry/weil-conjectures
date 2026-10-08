+++
id = "sk-thm-fe"
kind = "section"
title = "Functional equation"
order = 2920
lean = ["AlgebraicGeometry.weilSign", "AlgebraicGeometry.WeilFunctionalEquation.alternatingProdEval_eq"]
uses = ["sk-def-roots", "sk-def-zeta", "sk-prop-reciprocity", "sk-thm-tracetodeterminant"]
+++
*Theorem (sketch).*

With the notation of [sk-def-roots], set

$$
\chi=\sum_{i=0}^{2d}(-1)^{i}b_i,\qquad
\varepsilon=(-1)^{\chi}q^{-d\chi/2}\prod_{i=0}^{2d}D_i^{(-1)^{i}}\in\{1,-1\}.
$$

Then

$$
Z(X_0,q^{-d}T^{-1})=\varepsilon\,q^{d\chi/2}T^{\chi}Z(X_0,T).
$$

The sign $\varepsilon$ is the normalized functional-equation sign.

## Proof

Substitute $q^{-d}T^{-1}$ into the factorization
$Z=\prod_iP_{i,\ell}^{(-1)^{i+1}}$ of [sk-thm-tracetodeterminant] and
replace each factor by [sk-prop-reciprocity]; reindexing $i\mapsto2d-i$
turns the product into $\prod_iP_{i,\ell}^{(-1)^{i+1}}$ again, times the
constant $\prod_i\bigl((-1)^{b_i}D_i^{-1}\bigr)^{(-1)^{i+1}}$ and the monomial
$T^{\sum_i(-1)^{i+1}(-b_i)}=T^{\sum_i(-1)^{i}b_i}=T^{\chi}$. The constant is
$\prod_iD_i^{(-1)^{i}}$ up to the sign $(-1)^{\sum_i(-1)^{i+1}b_i} =(-1)^{-\chi}=(-1)^{\chi}$. By [sk-prop-reciprocity] $d\chi$ is even, so
$q^{d\chi/2}$ is defined and the constant is
$\varepsilon q^{d\chi/2}$; this is the displayed identity.

Uses: [sk-def-roots], [sk-def-zeta], [sk-prop-reciprocity], [sk-thm-tracetodeterminant]
