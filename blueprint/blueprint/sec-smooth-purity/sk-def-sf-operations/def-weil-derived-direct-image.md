+++
id = "def-weil-derived-direct-image"
kind = "definition"
title = "Derived direct image"
order = 1468
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-derived-cohomology-sheaves", "def-weil-derived-complete-integral-detailed", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties"]
+++
Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and put $A=A_{E,n}$. Let $X,Y$ be schemes on which $\ell$ is
invertible, and let $f:X\to Y$ be a morphism
[def-weil-scheme-morphism-properties]; write $f_n$ for this morphism at
coefficient level $A_{E,n}$. On the small pro-etale sites
[def-weil-pbc-proetale-site], with derived pullback and internal
Hom notation [def-weil-derived-pullback-tensor-hom] and derived tensor
notation [def-weil-derived-tensor], the functor
$f_*:\Sh(X_{\mathrm{proet}},A)\to\Sh(Y_{\mathrm{proet}},A)$ is left exact. At
finite level, choose a K-injective resolution and define its total
right-derived functor by

$$
 Rf_{*,n}=R(f_n)_*:D(X_{\mathrm{proet}},A_{E,n})
 \longrightarrow D(Y_{\mathrm{proet}},A_{E,n}).
$$

For a derived-complete integral [def-weil-derived-complete-integral-detailed]
complex $K\in D^b_c(X,\mathcal O_E)$, define

$$
 Rf_*K=
 R\varprojlim_n\operatorname{Res}_n Rf_{*,n}
 \bigl(K\otimes^L_{\mathcal O_E}A_{E,n}\bigr).
$$

The tower maps are induced by $A_{E,n+1}\twoheadrightarrow A_{E,n}$. The
finite-reduction comparison is the natural map

$$
 (Rf_*K)\otimes^L_{\mathcal O_E}A_{E,n}
 \longrightarrow
 Rf_{*,n}\bigl(K\otimes^L_{\mathcal O_E}A_{E,n}\bigr);
$$

its being an isomorphism, and its compatibility with composition and scalar
extension, are separate comparison assertions, not part of this definition of
the derived direct image. Here $A_{E,n}$ and finite-level constructibility
are the finite-torsion coefficient data
[def-weil-finite-torsion-constructibility], and $\mathcal H^r$ is the
cohomology-sheaf functor [def-weil-derived-cohomology-sheaves]. For
$\Lambda=E$ use the rationalized category
[def-weil-rationalization-karoubi]; for $\Lambda=\Qlb$ use the common-stage
category [def-weil-algebraically-closed-coefficients].
