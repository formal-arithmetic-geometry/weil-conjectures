+++
id = "thm-sf-dual-base-change"
kind = "theorem"
title = "Dual base change"
order = 2234
uses = ["def-exchange-projection", "def-sf-datum", "fix-prop-adjunctions", "lem-sf-mate", "lemma-weil-pbc-prime-proper-base-change", "sbc-thm-smooth-base-change", "thm-cbc-complete-proetale", "thm-cbc-finite-extension", "thm-cbc-finite-level-proetale", "thm-cbc-finite-torsion", "thm-cbc-qbar", "thm-weil-pbc-bounded-below", "thm-weil-pbc-complete-proetale", "thm-weil-pbc-finite-level-proetale", "thm-weil-pbc-qbar"]
+++
In the setting of [def-sf-datum], let

$$
\begin{array}{ccc}
X' & \xrightarrow{g'} & X\\
f'\downarrow && \downarrow f\\
Y' & \xrightarrow{g} & Y
\end{array}
$$

be a Cartesian square of separated finite-type $S$-schemes. Then there is a
canonical isomorphism, natural in the square and compatible with the pasting
of squares,

$$
Rf^!Rg_*\xrightarrow{\ \sim\ }Rg'_*Rf'^!,
$$

the right adjoint of the base-change isomorphism
$\operatorname{Ex}_!:Lg^*Rf_!\cong Rf'_!Lg'^*$. If $g$ is proper, so that
$g'$ is proper as well and $Rg_!=Rg_*$, $Rg'_!=Rg'_*$ by [fix-prop-adjunctions],
the same isomorphism reads

$$
Rf^!Rg_!\xrightarrow{\ \sim\ }Rg'_!Rf'^!.
$$

## Proof

The map $\operatorname{Ex}_!$ is the canonical exchange of
[def-exchange-projection]; that it is an isomorphism is axiom (A2), and
in the concrete setting it is the assertion of the compact-support
base-change theorem of the compact-support chapter
([thm-cbc-qbar], with the finite-coefficient, pro-étale and finite-extension forms [thm-cbc-finite-torsion], [thm-cbc-finite-level-proetale], [thm-cbc-complete-proetale], [thm-cbc-finite-extension]) at the coefficient stage
$\Lambda$, with the proper case and the finite-type case supplied by the
proper-base-change theorems of the proper-base-change chapter
([lemma-weil-pbc-prime-proper-base-change], [thm-weil-pbc-bounded-below], [thm-weil-pbc-finite-level-proetale], [thm-weil-pbc-complete-proetale], [thm-weil-pbc-qbar]) and the smooth case by the
smooth-base-change theorems of the smooth-base-change chapter
([sbc-thm-smooth-base-change]). The right adjoint of the composite
$Lg^*Rf_!$ is the composite of the right adjoints in the reverse order,
$Rf^!Rg_*$, and the right adjoint of $Rf'_!Lg'^*$ is $Rg'_*Rf'^!$: both
adjunctions are the ones of [def-sf-datum](A1), and they are the
adjunctions proved in [fix-prop-adjunctions]. An isomorphism of
functors induces an isomorphism between their right adjoints by the
uniqueness of adjoints, and the induced map is the mate of
$\operatorname{Ex}_!$ along the two pasted adjunctions, hence natural and
compatible with pasting by [lem-sf-mate]. The second assertion
substitutes the properness identification $Rg_!=Rg_*$ of
[fix-prop-adjunctions], which is stable under base change because
properness is ([lemma-weil-pbc-prime-proper-base-change] for the square).
