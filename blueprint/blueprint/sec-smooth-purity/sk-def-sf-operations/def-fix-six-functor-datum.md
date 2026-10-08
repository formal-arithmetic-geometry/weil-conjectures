+++
id = "def-fix-six-functor-datum"
kind = "definition"
title = "Six-functor datum"
order = 1491
uses = ["def-compact-support-direct-image-detailed", "def-exchange-projection", "def-weil-algebraically-closed-coefficients", "def-weil-derived-complete-integral-detailed", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-adjoint-admissibility", "def-weil-exceptional-inverse-image", "def-weil-extension-by-zero", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-integral-rational-qbar-compact-support", "def-weil-pbc-proetale-site", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties", "prop-compactification-coherence-detailed"]
+++
Fix the global finite-field datum
$(p,a,q,k_0,k)$, a prime $\ell\neq p$, a finite extension
$E/\Ql$ with valuation ring $\mathcal O_E$ and uniformizer
$\varpi_E$, and $n\in\mathbf Z_{\geq1}$; put
$A=A_{E,n}$ and $\Lambda\in\{A,\mathcal O_E,E,\Qlb\}$, with the
finite-torsion
constructibility, derived
completion, rationalization,
and
common-stage scalar
extension conventions of the preceding sections. Let $X,Y$ be
finite-type $k$-schemes,
let $f:X\to Y$ be a
separated morphism of
finite type, and let $j:U\hookrightarrow X$ be an
open immersion. On the
small pro-etale sites use the
bounded constructible categories $D^b_c(-,\Lambda)$ and the
finite-Tor subcategories
$D^b_{ctf}(-,\Lambda)$. The *six-functor operation datum* of the blueprint
consists of:

1. the derived pullback $Lf^*$, the derived tensor
$-\otimes^L_{\Lambda}-$, and the derived internal Hom
$R\mathcal Hom_{\Lambda}(-, -)$, as in
the derived pullback,
tensor, and internal Hom operations, and the derived direct image
$Rf_*$, as in
the derived direct image;
1. the extension-by-zero functor $j_!$, as in
extension by zero, and the
compact-support direct image $Rf_!$, as in
the compactification
independent compact-support direct image at the finite level and
the integral,
rational, and algebraically closed compact-support functors at the
higher levels, with the compactification-comparison isomorphisms and
the composition law
$R(g\circ f)_!\xrightarrow{\sim}Rg_!Rf_!$ recorded there (the
candidate-level verification of the comparisons for refinements is
[prop-compactification-coherence-detailed]); when $f$ is
proper, the
identification $Rf_!\xrightarrow{\sim}Rf_*$ is the one of
[def-compact-support-direct-image-detailed] for the compactification
$j=\operatorname{id}$, $p=f$;
1. the exchange transformations $\operatorname{Ex}_*$ and
$\operatorname{Ex}_!$ and the projection transformation
$\operatorname{PF}$, as in
the exchange and projection
transformations;
1. the exceptional inverse image
$$
Rf^!:D^b_c(Y,\Lambda)\longrightarrow D^b_c(X,\Lambda),
$$
the right adjoint of $Rf_!$ on the bounded constructible categories, as in
the exceptional inverse
image notation [def-weil-exceptional-inverse-image]: the constructible
exceptional adjoint, transported from the etale one, whose existence and
adjunction, interval boundedness, finite-Tor preservation, and refinement
compatibility of units and counits are theorems for every separated
finite-type morphism of finite-type $k$-schemes (thm-sf-ambient-adjoint-class,
thm-sf-preservation-class); the ambient notion
exceptional-adjoint
admissibility is not assumed, its clause (1) being false in general;
1. the dualizing objects $\omega_{X,\Lambda}=Ra_X^!\Lambda$ and
the Verdier dual $D_X(-)=R\mathcal Hom_{\Lambda}(-,\omega_{X,\Lambda})$,
formed from the exceptional adjoint and the derived internal Hom already
listed above, for every separated finite-type $X$.

This definition names operations and their construction data. It asserts
neither smooth purity nor Verdier biduality. Preservation of the displayed
constructible domains is established by the separate operation theorems;
the adjoint is the constructible one, available without hypothesis.
