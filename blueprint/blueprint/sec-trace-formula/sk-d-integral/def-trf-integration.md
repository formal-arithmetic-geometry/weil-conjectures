+++
id = "def-trf-integration"
kind = "definition"
title = "Integration along the structure morphism"
order = 2283
uses = ["def-compact-support-direct-image-detailed", "def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-dualizing-complex", "def-weil-derived-direct-image", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, $s=\Spec k$, and let $\beta$ be
separated finite type
and proper over $s$,
with structure morphism
$a_\beta:\beta\to s$ is exceptionally
admissible and $\omega_{\beta,A}$ the
dualizing complex of
[def-trf-dualizing-complex]. The *integration* (the
``trace along $a_\beta$'') is the map

$$
\int_\beta:
\Hom_{D(\beta,A)}\bigl(A_\beta,\omega_{\beta,A}\bigr)\longrightarrow A
$$

sending $\tau:A_\beta\to\omega_{\beta,A}$ to the composite

$$
A\xrightarrow{\ \eta^*\ }
R\Gamma(\beta,A_\beta)
\xrightarrow{R\Gamma(\tau)}
R\Gamma(\beta,\omega_{\beta,A})
\xrightarrow{\ \varepsilon_{a_\beta}\ }A,
$$

where the first arrow is the composite

$$
A=R\Gamma(s,A_s)
\xrightarrow{\ R\Gamma(s,\eta_\beta)\ }
R\Gamma(s,Ra_{\beta*}A_\beta)
\xrightarrow{\ \sim\ }
R\Gamma(s,Ra_{\beta!}A_\beta)=R\Gamma(\beta,A_\beta),
$$

whose first map is $R\Gamma(s,-)$ applied to the unit of the
adjunction $La_\beta^*\dashv Ra_{\beta*}$ of the
derived direct image, and
whose second is the identification $Ra_{\beta*}\cong Ra_{\beta!}$ for
the proper $a_\beta$
of [def-compact-support-direct-image-detailed] (so that
$R\Gamma(\beta,-)=R\Gamma(s,Ra_{\beta!}-)$); and the last arrow is
the composite

$$
R\Gamma(\beta,\omega_{\beta,A})
=R\Gamma(s,Ra_{\beta!}Ra_\beta^!A_s)
\xrightarrow{\ R\Gamma(s,\varepsilon_{a_\beta})\ }
R\Gamma(s,A_s)=A,
$$

where $\varepsilon_{a_\beta}$ is the counit of the adjunction
$Ra_{\beta!}\dashv Ra_\beta^!$ of
[def-trf-admissibility], applied to
$\omega_{\beta,A}=Ra_\beta^!A_s$ of
[def-trf-dualizing-complex].
