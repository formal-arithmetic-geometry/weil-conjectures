+++
id = "lem-sf-class-compact-support-comparison"
kind = "lemma"
title = "On the coefficient class the compact-support functor is computed on the étale site"
order = 1806
uses = ["def-amb-etale-compact-support", "def-compact-support-direct-image-detailed", "def-weil-compactifications-refinements", "def-weil-extension-by-zero", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-extension-by-zero", "def-weil-pbc-site-comparison-morphism", "def-weil-scheme-morphism-properties", "lem-cbc-proetale-extension-zero-comparison", "prop-weil-pbc-comparison-direct-image"]
+++
Let $K_0$ be a field, let $X,Y$ be
finite-type
$K_0$-schemes, let $f:X\to Y$ be a
separated finite-type
$K_0$-morphism with a
compactification
$X\xrightarrow{j}\overline X\xrightarrow{p}Y$, and let $A=A_{E,n}$.
Write $Rf_{!,n}=Rp_*j_!$ for the pro-étale
compact-support functor
attached to that compactification, the extension by zero being the
pro-étale one and $Rp_*$ the
derived direct image, and write
$Rf_!^{\Et}=Rp_{\Et,*}j_!^{\Et}$ for the étale compact-support functor
attached to the same compactification, that of
[def-amb-etale-compact-support], its extension by zero being the
étale one and its proper
direct image $Rp_{\Et,*}$. Let $G\in\Dplus(X_{\Et},A)$ be a
bounded-below complex of $A$-module sheaves on $X_{\Et}$, and let
$K\in\Dplus(X_{\Proet},A)$ come from the étale site with
witness $(G,\alpha)$,
$\alpha:\nu_X^*G\xrightarrow{\sim}K$. Then the canonical comparison

$$
Rf_{!,n}K\xrightarrow{\ \sim\ }\nu_Y^*\bigl(Rf_!^{\Et}G\bigr)
$$

is an isomorphism, natural in the witness.

## Proof

Fix the compactification $(j,p)$: $Rf_{!,n}$ is the candidate of
[def-compact-support-direct-image-detailed] attached to it, and $Rf_!^{\Et}$
is the étale candidate attached to the same one, so it suffices to
compare them there. The complex $K$ comes from the étale site with a
witness in the sense of
[def-weil-pbc-etale-origin-witness]. On the pro-étale
site $j_!$ is the exact
extension by zero of
[def-weil-extension-by-zero], on the étale site it is the exact
extension by zero of
[def-weil-pbc-extension-by-zero], and
[lem-cbc-proetale-extension-zero-comparison] identifies them along the
comparison morphism of [def-weil-pbc-site-comparison-morphism]:

$$
\nu_{\overline X}^*j_!^{\Et}\xrightarrow{\ \sim\ }j_!\nu_X^* .
$$

That identification is natural in the coefficient sheaf and both functors
are exact, so, applied degreewise to the bounded-below complex $G$, it
gives an isomorphism of complexes
$\nu_{\overline X}^*j_!^{\Et}G\cong j_!\nu_X^*G$, compatible with the
differentials. The witness identifies $K$ with $\nu_X^*G$, whence
$Rf_{!,n}K\cong Rp_*j_!\nu_X^*G$. The proper morphism $p$ is of finite
type, hence quasi-compact and quasi-separated, and $j_!^{\Et}G$ is a
bounded-below complex on $\overline X_{\Et}$, so the comparison direct
image [prop-weil-pbc-comparison-direct-image] applied to $u=p$ and
$L=j_!^{\Et}G$ gives

$$
Rp_*\bigl(\nu_{\overline X}^*j_!^{\Et}G\bigr)
\cong\nu_Y^*\bigl(Rp_{\Et,*}j_!^{\Et}G\bigr)
=\nu_Y^*\bigl(Rf_!^{\Et}G\bigr).
$$

Composing the two isomorphisms gives the displayed comparison. Naturality
in the witness is the naturality of the extension-by-zero comparison, of
the comparison direct image, and of the witness identification. No
constructibility is used, and the étale compact-support functor is the
candidate of [def-amb-etale-compact-support] attached to the same
compactification: it is the functor denoted $Rf_!$ in the
ambient-smooth-duality chapter and written $Rf_!^{\Et}$ here to separate
it from the pro-étale functor.
