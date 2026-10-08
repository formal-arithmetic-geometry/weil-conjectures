+++
id = "lem-compact-support-direct-image-triangulated"
kind = "lemma"
title = "Triangulatedness of the finite-level compact-support direct image"
order = 1493
uses = ["def-compact-support-direct-image-detailed", "def-weil-compact-support-candidate", "def-weil-compactifications-refinements", "def-weil-derived-direct-image", "def-weil-extension-by-zero", "def-weil-finite-torsion-constructibility", "def-weil-scheme-morphism-properties", "lem-weil-extension-by-zero-exact"]
+++
Let $K_0$ be a field, let $X,Y$ be finite-type
[def-weil-scheme-morphism-properties] $K_0$-schemes, and let $f:X\to Y$ be a
separated finite-type $K_0$-morphism. Fix a prime $\ell$, write
$\Ql=\mathbf Q_\ell$, and require that its image in $K_0$ is invertible.
Choose a finite extension $E/\Ql$, an integer $n\in\mathbf Z_{\geq1}$, and
put $A=A_{E,n}$. For every object $c\in\operatorname{Comp}(f)$ of the
compactification category [def-weil-compactifications-refinements], the
functor

$$
 Rf_{!,n}=Rf_{!,n}^{c}:
 D(X_{\mathrm{proet}},A_{E,n})\longrightarrow D(Y_{\mathrm{proet}},A_{E,n})
$$

of [def-compact-support-direct-image-detailed] is a triangulated functor: it
preserves shifts and carries distinguished triangles to distinguished
triangles.

## Proof

Write $c=(j,\bar f)$, so that $j$ is an open immersion
[def-weil-scheme-morphism-properties], $\bar f$ is proper, and, by
[def-weil-compact-support-candidate], the candidate attached to $c$ in the
compactification category [def-weil-compactifications-refinements] is
$Rf_{!,n}^{c}=R\bar f_{*,n}\,j_!$. The extension-by-zero functor
[def-weil-extension-by-zero] $j_!$ is exact by
[lem-weil-extension-by-zero-exact], and the derived direct image
[def-weil-derived-direct-image] $R\bar f_{*,n}$ is computed by a K-injective
resolution, hence carries distinguished triangles of $D(\overline
X_{\mathrm{proet}},A_{E,n})$ to distinguished triangles of
$D(Y_{\mathrm{proet}},A_{E,n})$. The composite $Rf_{!,n}=Rf_{!,n}^{c}$ of
[def-compact-support-direct-image-detailed] therefore preserves shifts and
distinguished triangles. The finite-torsion coefficients of
[def-weil-finite-torsion-constructibility] enter only through the ambient
categories, so the argument applies verbatim to every object
$c\in\operatorname{Comp}(f)$.
