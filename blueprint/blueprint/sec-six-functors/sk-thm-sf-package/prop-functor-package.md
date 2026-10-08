+++
id = "prop-functor-package"
kind = "theorem"
title = "Coefficient and functor package on the proved domains"
order = 2256
tags = ["latex:proposition"]
uses = ["cor-cbc-proper-coincidence", "cor-coef-integral-internal-hom", "cor-weil-boundary-duality-discharge", "cor-weil-finite-constructible-hom", "def-fix-six-functor-datum", "fix-cor-verdier-exchange", "fix-lem-exchanges", "fix-prop-coherence", "fix-prop-projection-formula", "lem-cbc-open-closed-recollement", "lem-coef-finite-direct-image", "lem-coef-finite-exceptional", "lem-coef-normalized-dvr-effectivity", "lem-coef-rational-operations", "lem-compact-support-direct-image-triangulated", "lem-fix-compact-support-coefficient-change", "lem-fix-operation-reduction", "lem-weil-coefficient-frobenius", "lem-weil-scalar-extension-exact-triangulated", "prop-coef-integral-exceptional-adjoint", "prop-compactification-coherence-detailed", "prop-weil-pbc-descent-functors", "sbc-thm-bounded-below-derived-smooth-base-change", "thm-cbc-finite-torsion", "thm-cbc-qbar", "thm-coef-finite-hom", "thm-coef-integral-verdier", "thm-coef-qbar-verdier", "thm-coef-rational-verdier", "thm-fix-general-biduality", "thm-pur-adic-reconstruction", "thm-pur-finite-coefficient-smooth-purity", "thm-pur-rational-and-qbar-purity", "thm-sf-comp-composition", "thm-sf-dual-perfect", "thm-weil-pbc-bounded-below", "thm-weil-pbc-idempotent-complete-triangulation", "thm-weil-pbc-qbar"]
+++
Use the coefficient stages $A_{E,n},\mathcal O_E,E,\Qlb$, finite-type
separated schemes over the fixed algebraic closure of a finite field, and separated
finite-type morphisms of [def-fix-six-functor-datum].
Pullback, tensor and the two direct images have their proved constructible
domains. At finite stages, internal Hom preserves bounded constructible
finite-Tor complexes in both variables by
[cor-weil-finite-constructible-hom].
General internal-Hom coefficient change is [thm-coef-finite-hom].
Integral internal Hom and exceptional inverse image preserve the
specified bounded constructible category by
[cor-coef-integral-internal-hom], [prop-coef-integral-exceptional-adjoint];
their field versions are [lem-coef-rational-operations], [thm-coef-qbar-verdier].
At finite coefficients the domain remains $D^b_{ctf}$; at integral
and field coefficients it is the specified $D^b_c$.
The sharper dimension-free Hom bound and tensor-dual formulas still
require a site-perfect first
argument. Exceptional adjunction here is on these constructible
categories, without asserting an unrestricted unbounded ambient adjoint.
The following seven clauses collect the preceding results.

1. Finite coefficient-field extension is exact. Compatible finite-stage
functors and transformations descend to the idempotent-complete common-stage
$\Qlb$-category.
1. Compactification comparisons for $Rf_!=R\bar f_*j_!$ are independent
of refinement and satisfy the cocycle condition. For a derived-complete
$\mathcal O_E$-object $K$, put
$K_n=K\otimes^L_{\mathcal O_E}A_{E,n}$. Then
$$
(Rf_*K)\otimes^L_{\mathcal O_E}A_{E,n}\simeq Rf_*K_n,
\qquad
(Rf_!K)\otimes^L_{\mathcal O_E}A_{E,n}\simeq Rf_!K_n.
$$
Between finite quotient rings, both direct-image coefficient comparisons
hold on the bounded finite-Tor domains. For a coherent normalized DVR
tower, the canonical reduction of its derived limit recovers its terms
by [lem-coef-normalized-dvr-effectivity]; uniform finite-level
bounds supply constructibility of the integral output. No such claim
is made for a tower whose normalization has not been proved.
1. Compact-support composition satisfies
$R(gf)_!\simeq Rg_!Rf_!$, with the identity and associativity equations.
For proper $f$, $Rf_!\simeq Rf_*$. For a closed immersion $i$
with open complement $j$, applying $Rf_!$ to the localization triangle gives
$$
R(fj)_!j^*K\longrightarrow Rf_!K\longrightarrow R(fi)_!i^*K\longrightarrow .
$$
1. In a Cartesian square, $g^*Rf_*\to Rf'_*g'^*$ is an isomorphism
if $f$ is proper or $g$ is smooth, and
$g^*Rf_!\simeq Rf'_!g'^*$ for arbitrary base change, on the stated
bounded coefficient domains: for $g^*Rf_*$ this means bounded-below
complexes with torsion cohomology at the finite stages, and
$D^b_c$ of the adic (pro-étale) categories at $\mathcal O_E$, $E$, $\Qlb$,
obtained from the finite stages by derived limits and transport; no claim is
made for discrete non-torsion coefficients on the small étale site.
1. For $K\in D^b_c(X,\Lambda)$ and $L\in D^b_{ctf}(Y,\Lambda)$,
the compact-support projection map is an isomorphism:
$$
Rf_!K\otimes^L L\simeq Rf_!(K\otimes^L f^*L).
$$
1. Smooth purity for relative dimension $r$ identifies
$Rf^!L\simeq f^*L(r)[2r]$, with its normalized trace, on the
admissible domains and coefficient stages proved in the purity chapter.
1. For separated finite-type $f:X\to Y$ and structure morphisms set
$\omega_X=Ra_X^!\Lambda$ and
$D_X=R\mathcal Hom(-,\omega_X)$. For
$M\in D^b_{ctf}(X,\Lambda)$, the formal Verdier exchange map of
[fix-cor-verdier-exchange] is a natural isomorphism
$$
D_YRf_!M\xrightarrow{\ \sim\ }Rf_*D_XM.
$$
Point biduality and smooth site-perfect biduality are proved independently.
At every finite stage $A=A_{E,n}$, the general anti-equivalence
$D_Y:D^b_{ctf}(Y,A)^{\mathrm{op}}\simeq D^b_{ctf}(Y,A)$, with
$D_Y^2\simeq\operatorname{id}$, is
[thm-fix-general-biduality]. Its geometric proof also supplies the
finite-stage boundary comparison in
[cor-weil-boundary-duality-discharge].
The coefficient comparisons and uniform bounds are proved separately
in [thm-coef-integral-verdier], [thm-coef-rational-verdier], [thm-coef-qbar-verdier].
They give the same anti-equivalence and evaluation-defined biduality
on $D^b_c(Y,\mathcal O_E)$, $D^b_c(Y,E)$, and $D^b_c(Y,\Qlb)$.
On these domains $Rf^!=D_Xf^*D_Y$, with its exceptional adjunction,
by [lem-coef-finite-exceptional], [prop-coef-integral-exceptional-adjoint], [lem-coef-rational-operations].

All comparisons have the coherence and equivariance proved for their
individual clauses. No clause enlarges the domain of another clause.

## Proof

The finite-stage internal-Hom preservation recorded before the clauses
is [cor-weil-finite-constructible-hom]; its coefficient comparison
is [thm-coef-finite-hom]. Integral preservation and field passage
are [cor-coef-integral-internal-hom], [lem-coef-rational-operations].
Clause (1) is [lem-weil-scalar-extension-exact-triangulated],
[prop-weil-pbc-descent-functors], and
[thm-weil-pbc-idempotent-complete-triangulation].
For (2), use [prop-compactification-coherence-detailed] and the independently
proved [lem-fix-operation-reduction], [lem-fix-compact-support-coefficient-change].
The ordinary finite quotient comparison is [lem-coef-finite-direct-image];
normalized tower reconstruction is [lem-coef-normalized-dvr-effectivity].
Clause (3) follows from [thm-sf-comp-composition], [fix-lem-exchanges],
[cor-cbc-proper-coincidence], and the image of
[lem-cbc-open-closed-recollement] under the exact functor of
[lem-compact-support-direct-image-triangulated].
Clause (4) is [thm-weil-pbc-bounded-below], [thm-weil-pbc-qbar],
[sbc-thm-bounded-below-derived-smooth-base-change], and
[thm-cbc-finite-torsion], [thm-cbc-qbar].
Clause (5) is [fix-prop-projection-formula].
Clause (6) is [thm-pur-finite-coefficient-smooth-purity],
[thm-pur-adic-reconstruction], and
[thm-pur-rational-and-qbar-purity].
For (7), the exchange is [fix-cor-verdier-exchange];
[lem-weil-coefficient-frobenius] proves the required point duality,
and [thm-sf-dual-perfect] reduces the smooth site-perfect
case to local perfect-complex biduality. General finite-stage biduality is
[thm-fix-general-biduality]; its proof establishes constructible
preservation first and then uses geometric generic restriction and
dimension induction. Boundary exchange is its consequence
[cor-weil-boundary-duality-discharge].
The integral and field anti-equivalences are
[thm-coef-integral-verdier], [thm-coef-rational-verdier], [thm-coef-qbar-verdier].
The exceptional adjunction and its coefficient comparisons are
[lem-coef-finite-exceptional], [prop-coef-integral-exceptional-adjoint], [lem-coef-rational-operations].
Finally apply [fix-prop-coherence].
Each ingredient has its own proof; this proposition is a terminal summary.
