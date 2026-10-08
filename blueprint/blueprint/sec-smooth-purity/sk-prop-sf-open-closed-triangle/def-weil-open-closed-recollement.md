+++
id = "def-weil-open-closed-recollement"
kind = "definition"
title = "Open--closed recollement"
order = 1834
uses = ["def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-extension-by-zero", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and put $A=A_{E,n}$. Let $Z,U,X$ be schemes on which $\ell$ is
invertible. Let $i:Z\hookrightarrow X$ be a closed immersion
[def-weil-scheme-morphism-properties] and let $j:U\hookrightarrow X$ be its
complementary open immersion. Write $i^*,j^*$ for the derived pullbacks
[def-weil-derived-pullback-tensor-hom], and use the exact
extension-by-zero functor [def-weil-extension-by-zero] $j_!$ and the derived
direct image [def-weil-derived-direct-image] $Ri_*$ on the small pro-etale
sites [def-weil-pbc-proetale-site]. For $K\in D^b_c(X,A)$, a
bounded complex with the finite-torsion constructibility condition
[def-weil-finite-torsion-constructibility], the canonical open--closed pair
of maps is

$$
 j_!j^*K\longrightarrow K\longrightarrow Ri_*i^*K,
$$

given by the open counit and the closed unit. An *open--closed recollement
triangle* means a distinguished triangle extending this specified pair. This
names the data and the required property; existence of this triangle is not
assumed in the definition. It will follow from the sheaf-level exact sequence
when the complementary open immersion is quasi-compact, in particular for the
Noetherian schemes used in the finite-field applications.
