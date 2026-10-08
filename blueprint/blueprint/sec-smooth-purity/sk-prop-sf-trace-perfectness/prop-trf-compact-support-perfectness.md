+++
id = "prop-trf-compact-support-perfectness"
kind = "theorem"
title = "Compact-support perfectness"
order = 1828
tags = ["latex:proposition"]
uses = ["def-compact-support-direct-image-detailed", "def-trf-categorical-trace", "def-trf-coefficient-conventions", "def-weil-finite-coefficient-point", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-full-cohomological-dimension", "def-weil-scheme-morphism-properties", "lem-exc-residue-tor-test", "lem-fix-compact-support-coefficient-change", "lem-trf-finite-tor-amplitude-perfect", "prop-finite-compact-support-constructibility", "prop-weil-pbc-inverse-image-exact"]
+++
Fix the global finite-field datum
and the coefficient
conventions, and let $K\in D^b_{ctf}(X,A)$ with structure morphism
$a_X:X\to\Spec k$ separated finite type. Then

$$
R\Gamma_c(X,K)\in D^b_{\mathrm{fin}}(A),
$$

and the derived geometric stalk $K_{\bar x}=L\bar x^*K$ lies in
$D^b_{\mathrm{fin}}(A)$ for every
geometric point
$\bar x$ of $X$.

## Proof

Let $C=R\Gamma_c(X,K)$, with compact support as in
[def-compact-support-direct-image-detailed], [def-trf-coefficient-conventions].
The finite-level constructibility theorem
[prop-finite-compact-support-constructibility] gives a bounded
complex on $\operatorname{Spec}k$ with finite cohomology modules,
using the point identification of
[def-weil-finite-coefficient-point]. This assertion alone does
not give perfectness over the finite local ring $A$.

Put $\kappa=A/(\varpi_E)$. The narrow coefficient-change result
[lem-fix-compact-support-coefficient-change], applied to
$A_{E,n}\to A_{E,1}=\kappa$, identifies

$$
C\otimes_A^L\kappa
\xrightarrow{\sim}R\Gamma_c(X,K\otimes_A^L\kappa).
$$

The input on the right is bounded constructible: finite Tor amplitude
gives boundedness, and its cohomology is constructible by restricting
to a finite constructible stratification and taking the derived
tensor of the finite coefficient modules, as in
[def-weil-finite-tor-amplitude], [def-weil-finite-torsion-constructibility].
Hence the right side is bounded by
[prop-finite-compact-support-constructibility] at the residue
coefficient stage. The residue-field criterion of
[lem-exc-residue-tor-test], applied on the point, now proves
that $C$ has finite Tor amplitude. Together with its finite
cohomology, [lem-trf-finite-tor-amplitude-perfect] shows that
$C$ is represented by a bounded complex of finite free
$A$-modules.

For $K_{\bar x}$, the exact inverse-image property
[prop-weil-pbc-inverse-image-exact] and the finite-stalk
condition of [def-weil-finite-torsion-constructibility] give
bounded finite cohomology. The tensor-vanishing definition
[def-weil-finite-tor-amplitude] is preserved by this inverse
image, so the same module-theoretic perfectness criterion applies.
Thus both objects lie in the perfect category used for categorical
trace in [def-trf-categorical-trace].
No preservation of finite Tor amplitude by a package summary is used
in this argument.

*Recorded in advance* from chapter *The trace formula* of the source.
