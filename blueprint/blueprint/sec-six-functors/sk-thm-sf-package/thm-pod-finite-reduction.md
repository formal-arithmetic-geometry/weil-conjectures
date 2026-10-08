+++
id = "thm-pod-finite-reduction"
kind = "theorem"
title = "Finite reduction of the Poincare pairing"
order = 2254
uses = ["def-pod-coefficient-dual-on-x", "def-pod-conventions", "def-pod-derived-poincare-pairing", "def-pur-smooth-trace", "def-weil-site-perfect-complex", "lem-fix-operation-reduction", "thm-pod-identification-of-the-comparison", "thm-pod-point-perfectness", "thm-pur-finite-reduction-of-purity", "thm-sf-dual-perfect"]
+++
Use the smooth Poincare setting, with
the admissible structure morphism and normalized smooth orientation.
Let $n\geq m\geq1$, put $A_n=\mathcal O_E/\varpi_E^n$ and
$A_m=\mathcal O_E/\varpi_E^m$, and let $K_n$ be a
site-perfect constructible
$A_n$-complex. Put $K_m=K_n\otimes^L_{A_n}A_m$.
The coefficient comparisons identify the reduction of the
derived Poincare pairing
for $K_n$ with the pairing for $K_m$. In particular, writing
$K_n^\vee$ for its coefficient dual,
the canonical isomorphisms make the square

$$
\begin{array}{ccc}
R\Gamma_c(X,K_n)^\vee\otimes^L_{A_n}A_m
&\xrightarrow{\beta_{K_n}^{\sharp,-1}\otimes1}&
R\Gamma(X,K_n^\vee(d))[2d]\otimes^L_{A_n}A_m\\
\downarrow\wr&&\downarrow\wr\\
R\Gamma_c(X,K_m)^\vee
&\xrightarrow{\beta_{K_m}^{\sharp,-1}}&
R\Gamma(X,K_m^\vee(d))[2d]
\end{array}
$$

commute. Here $\beta^{\sharp,-1}$ denotes the inverse of the
tensor–Hom adjoint of the pairing.

## Proof

The compact-support, tensor, site-perfect internal-Hom and evaluation
comparisons are [lem-fix-operation-reduction]. Thus the coefficient dual of
[def-pod-coefficient-dual-on-x], the cup product and evaluation
in [def-pod-derived-poincare-pairing], and their adjunction maps
all reduce compatibly. The remaining geometric ingredient is the
normalized trace of [def-pur-smooth-trace]; its coefficient
compatibility, together with that of the smooth orientation, is
[thm-pur-finite-reduction-of-purity].
The identification in [thm-sf-dual-perfect] uses
that orientation and the same internal-Hom operations.
Composing these commuting squares gives the square for the pairing,
using the canonical coefficient comparison on ordinary global sections;
no isomorphism assertion for that map is needed at this step.
By [thm-pod-point-perfectness] the compact-support complex is
perfect, so its coefficient dual commutes with reduction and the left
vertical map is an isomorphism. At each coefficient stage,
[thm-pod-identification-of-the-comparison] identifies the adjoint
of the pairing with the duality isomorphism. Taking adjoints in the
commuting pairing square therefore proves that the ordinary-global-section
comparison on the right is an isomorphism too. Taking inverses of the
horizontal adjoints gives exactly the displayed square.
No flatness of $A_m$ over $A_n$ is asserted: every reduction is
derived, and the coefficient-dual comparisons use the stated
perfectness hypothesis.
