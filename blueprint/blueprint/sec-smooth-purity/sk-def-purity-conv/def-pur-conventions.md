+++
id = "def-pur-conventions"
kind = "definition"
title = "Purity coefficient conventions"
order = 1889
uses = ["def-coefficient-twists-detailed", "def-compact-support-direct-image-detailed", "def-exchange-projection", "def-sbc-smooth-morphisms", "def-weil-algebraically-closed-coefficients", "def-weil-derived-cohomology-sheaves", "def-weil-derived-complete-integral-detailed", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-frobenius-coefficient-twists", "def-weil-pbc-proetale-site", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties"]
+++
Fix the global finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, a prime $\ell\neq p$, a finite
extension $E/\Ql$ contained in a fixed algebraic closure $\Qlb$, with
valuation ring $\mathcal O_E$, a uniformizer $\varpi_E$, and an
integer $n\in\mathbf Z_{\geq1}$. Put $A=A_{E,n}$. On the
small pro-etale site, use the
bounded constructible
finite-torsion coefficient category $D^b_c(-,A)$, the
finite-Tor subcategories
$D^b_{ctf}(-,\Lambda)$ for $\Lambda\in\{A,\mathcal O_E,E,\Qlb\}$, the
derived pullback, tensor,
and internal Hom, the
[def-weil-derived-cohomology-sheaves] cohomology sheaves
$\mathcal H^r$, the
compact-support direct image
$Rf_!$, and the
exceptional inverse image
$Rf^!$, with $Rf_!\dashv Rf^!$ and the
exchange and projection and [def-weil-exceptional-inverse-image]). Use the
coefficient twists of degree
$m\in\mathbf Z$,

$$
K(m)=K\otimes^L_{\Lambda_Y}\Lambda(m),
$$

and the terminology
smooth of relative dimension
$d\in\mathbf Z_{\geq0}$. For $\Lambda=A$ all statements and
constructions below are made; the
derived-complete integral,
rationalized, and
common-stage
algebraically closed versions for $\mathcal O_E,E,\Qlb$ are the
coefficient transports described in the transport section at the end of
this blueprint. Geometric Frobenius acts on the
twists with the specified
twist normalization of the framework chapter: by $q^{-1}$ on $\Lambda(1)$, by
$q^{-m}$ on $\Lambda(m)$, and by $q^{m}$ on $\Lambda(-m)$ for
$m\geq0$. For $a:Y\to\Spec k$ write

$$
\omega_{Y,\Lambda}=Ra^!\Lambda.
$$
