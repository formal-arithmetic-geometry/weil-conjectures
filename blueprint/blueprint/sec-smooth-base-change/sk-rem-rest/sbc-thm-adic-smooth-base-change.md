+++
id = "sbc-thm-adic-smooth-base-change"
kind = "theorem"
title = "Adic smooth base change"
order = 1443
uses = ["def-sbc-smooth-morphisms", "def-weil-pbc-completed-pullback", "lemma-weil-pbc-perfect-projection-formula", "sbc-def-base-change-square", "sbc-thm-finite-proetale-smooth-base-change", "sbc-thm-smooth-base-change", "thm-weil-pbc-complete-proetale"]
+++
In the square of
[sbc-thm-smooth-base-change], assume $f$ smooth, $g$ quasi-compact
and quasi-separated, all schemes noetherian, $\ell$ invertible on $S$,
and let $A=\mathcal O_E$ with ideal $I=(\varpi)$ such that every
$A_n=A/I^{n+1}$ is finite of order invertible on the schemes under
consideration and perfect as an $A$-module. Let
$K\in\Dbc(T_{\Proet},A)$ with each reduction $K_n$ in the essential
image of $\Dbc(T_{\Et},A_n)$. Then the completed exchange map

$$
Lf^*_{\mathrm{comp}}Rg_{*,\mathrm{comp}}K
\xrightarrow{\ \sim\ }Rh_{*,\mathrm{comp}}Le^*_{\mathrm{comp}}K
$$

is an isomorphism in the derived-complete category, and in
$\Dbc(S_{\Proet},A)$ whenever the four finite-level systems involved
have constructible cohomology in one common finite cohomological
interval.

## Proof

The completed actions of [def-weil-pbc-completed-pullback] are the
derived inverse limits of their finite levels; direct image commutes
with derived limits and derived completion
([thm-weil-pbc-complete-proetale]), the perfect projection formula
of [lemma-weil-pbc-perfect-projection-formula] identifies the
finite levels of the two sides with the finite-level exchanges, and
each finite-level exchange is an isomorphism by
[sbc-thm-finite-proetale-smooth-base-change]; derived inverse
limits of isomorphisms are isomorphisms, and the constructible hypothesis
gives the indicated landing.
