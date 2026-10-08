+++
id = "fix-lem-tensor-adjunction"
kind = "lemma"
title = "Tensor–adjunction form of the exchange"
order = 2116
uses = ["def-fix-six-functor-datum", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-adjoint-admissibility", "fix-prop-adjunctions", "fix-prop-projection-formula", "lemma-weil-pbc-geometric-stalk-conservative", "thm-weil-pbc-site-comparison"]
+++
In the six-functor datum of
[def-fix-six-functor-datum], let $f$ be
exceptionally
admissible, and let $M\in D^b_{ctf}(X,\Lambda)$ and
$N\in D^b_{ctf}(Y,\Lambda)$. There is a canonical isomorphism

$$
Rf_*R\mathcal Hom_X\bigl(M,f^!N\bigr)
\xrightarrow{\ \sim\ }
R\mathcal Hom_Y\bigl(Rf_!M,N\bigr),
$$

natural in $M$ and $N$, compatible with finite reduction, scalar
extension, and shifts.

## Proof

Step 1: the construction. For every
$L\in D^b_{ctf}(Y,\Lambda)$, the derived tensor–internal-Hom
adjunction of [def-weil-derived-pullback-tensor-hom] and the
adjunction of [fix-prop-adjunctions] give the chain

$$
\begin{aligned}
\Hom_Y\bigl(L,R\mathcal Hom_Y(Rf_!M,N)\bigr)
&\cong\Hom_Y(Rf_!M\otimes^L_{\Lambda}L,N)\\
&\cong\Hom_Y\bigl(Rf_!(M\otimes^L_{\Lambda}Lf^*L),N\bigr)\\
&\cong\Hom_X\bigl(M\otimes^L_{\Lambda}Lf^*L,f^!N\bigr)\\
&\cong\Hom_X\bigl(Lf^*L,R\mathcal Hom_X(M,f^!N)\bigr)\\
&\cong\Hom_Y\bigl(L,Rf_*R\mathcal Hom_X(M,f^!N)\bigr),
\end{aligned}
$$

where the second isomorphism is the inverse of the projection formula
of [fix-prop-projection-formula] (applicable since $M$ and
$L$ lie in the finite-Tor subcategories), and the first, third, and
fourth are the tensor–internal-Hom adjunction of
[def-weil-derived-pullback-tensor-hom] with the adjunction
$Rf_!\dashv Rf^!$ of [fix-prop-adjunctions], the last being
the adjunction $Lf^*\dashv Rf_*$ of
[fix-prop-adjunctions]. Step 2: detection. The adjunction chain
defines a canonical map of the two ambient derived objects.
At a finite etale coefficient stage, take
$L=e_!A[r]$, where $e:V\to Y$ is a quasi-compact etale object
of the site and $r\in\mathbf Z$. Such an extension by zero is
constructible and flat, so it is in the finite-Tor domain used in
step 1. The resulting Hom groups are the cohomology of the two
objects on $V$. The cone therefore has zero cohomology on every
such $V$, and hence has zero geometric stalks. Conservativity in
[lemma-weil-pbc-geometric-stalk-conservative] proves the map is
an isomorphism without first assuming that either output belongs to
the finite-Tor subcategory. The site equivalence on the stipulated
coefficient categories in [thm-weil-pbc-site-comparison] and
the coefficient comparisons of the four ingredients give the stated
realizations and field stages. Naturality and the comparison squares
under reduction follow by transposing them to the same tensor and
counit composites. This asserts compatibility of the specified maps;
it does not supply a separate internal-Hom reduction isomorphism
outside the domains where that comparison has been proved.
