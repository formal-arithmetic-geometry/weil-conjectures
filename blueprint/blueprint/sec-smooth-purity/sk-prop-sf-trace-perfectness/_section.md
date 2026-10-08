+++
id = "sk-prop-sf-trace-perfectness"
kind = "section"
title = "Perfectness of compact cohomology and of geometric stalks"
order = 1822
lean = ["AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt", "AlgebraicGeometry.Etale.finite_compactlySupportedCohomology"]
+++
*Proposition (sketch).*

Let $\Lambda=A_{E,n}$, let $X$ be separated of finite type over $k$ with
structure morphism $a_X$, and let $K\in\Dctf(X,\Lambda)$. Then
$\RG_c(X,K)=Ra_{X!}K$ is a perfect complex of $\Lambda$-modules, and so is the
derived geometric stalk $K_{\bar x}=L\bar x^*K$ at every geometric point
$\bar x$ of $X$.
Chapter 19 (the trace formula), prop:trf-compact-support-perfectness:
boundedness and constructibility, then finiteness of the cohomology modules,
then the commutative-algebra step that over the Artinian local ring $A_{E,n}$ a
bounded complex with finite cohomology modules is perfect exactly when it has
finite Tor amplitude.

Uses: `prop-trf-compact-support-perfectness`
