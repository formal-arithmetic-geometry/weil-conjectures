+++
id = "thm-pur-projective-bundle-formula"
kind = "theorem"
title = "Projective-bundle formula without purity"
order = 1986
uses = ["cor-kun-compact-kunneth", "cor-weil-pbc-geometric-fiber-finite", "def-coefficient-twists-detailed", "def-pur-conventions", "def-weil-derived-cohomology-sheaves", "def-weil-open-closed-recollement", "def-weil-scheme-morphism-properties", "lem-pur-divisor-class", "lem-pur-frame-independence", "lem-pur-kummer-additivity", "lem-pur-kunneth-supported", "prop-weil-proet-finite-proper-base-change", "thm-pur-rank-one-local-calculation", "thm-pur-rank-one-thom"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $F$ be a
vector bundle of rank
$n+1$ on $B$, let $p:\mathbf P_B(F)\to B$, and put
$h_F=c_1(\mathcal O(1))$ of [lem-pur-kummer-additivity].
Then the morphism

$$
(1,h_F,\ldots,h_F^n):
\bigoplus_{a=0}^{n}\Lambda_B(-a)[-2a]
\xrightarrow{\ \sim\ }Rp_*\Lambda_{\mathbf P_B(F)}
$$

is an isomorphism, base-change compatible. This statement uses no
purity isomorphism.

## Proof

The vanishing of a bounded cone will be checked on its cohomology sheaves in the sense of [def-weil-derived-cohomology-sheaves].
Step 1: the field case. Let the base be an algebraically closed
field and write $H=\mathbf P^{n-1}$ for the hyperplane at infinity
of $\mathbf P^n$, with complement $\mathbf A^n$. By
[thm-pur-rank-one-thom] on the fiber-wise structure, the Künneth
formula for compactly supported cohomology
[cor-kun-compact-kunneth] of the Künneth chapter — the
*compact-support* statement, which is not the closed-support Künneth
[lem-pur-kunneth-supported]: cohomology with support in the whole space
is ordinary cohomology, whereas $R\Gamma_c$ is computed on a
compactification — and induction,

$$
R\Gamma_c(\mathbf A^n,\Lambda)\;\cong\;\Lambda(-n)[-2n].
$$

Apply the open–closed localization triangle of
[def-weil-open-closed-recollement] to
$\mathbf A^n\subset\mathbf P^n$. By induction on $n$,
restriction to $H$ identifies $1,h,\ldots,h^{n-1}$ with the
corresponding basis of $R\Gamma(H,\Lambda)$, and the remaining class
$h^n$ restricts to zero on $H$. Choose $n$ hyperplanes whose
intersection is the origin of the affine chart; the product of their
localized Kummer classes is supported at the origin, and after
forgetting support and extending to $\mathbf P^n$ it is
$h^n$; under the Künneth isomorphism this supported product is the
generator of
$R\Gamma_c(\mathbf A^n,\Lambda)=\Lambda(-n)[-2n]$ fixed by the
rank-one normalization ([thm-pur-rank-one-local-calculation]).
Therefore

$$
\bigoplus_{a=0}^{n}\Lambda(-a)[-2a]
\xrightarrow{\ (1,h,\ldots,h^n)\ }R\Gamma(\mathbf P^n,\Lambda)
$$

is an isomorphism.

Step 2: the general base. The Kummer class $h_F$ is global; the
class of the divisors in Step 1 is the one of
[lem-pur-divisor-class] (the frame class of the
$\mathbf P^n$-bundle, with the independence of
[lem-pur-frame-independence]), so the morphism of the statement
is defined before taking any fiber. Proper base change
([prop-weil-proet-finite-proper-base-change]) with
[cor-weil-pbc-geometric-fiber-finite] identifies its pullback to
each geometric point of $B$ with the calculation of Step 1; the
cone is bounded constructible with zero geometric stalks, hence zero.
The same argument for the pullbacks proves base-change compatibility.
This proof used only the rank-one Thom calculation, Künneth,
localization, and proper base change.
