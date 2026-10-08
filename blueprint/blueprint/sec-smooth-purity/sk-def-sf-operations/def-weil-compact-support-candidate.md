+++
id = "def-weil-compact-support-candidate"
kind = "definition"
title = "Compact-support candidate attached to a compactification"
order = 1472
uses = ["def-weil-compactifications-refinements", "def-weil-derived-direct-image", "def-weil-extension-by-zero", "def-weil-finite-torsion-constructibility", "def-weil-pbc-etale-origin-witness", "def-weil-scheme-morphism-properties"]
+++
Let $K_0$ be a field, let $X,Y$ be finite-type
[def-weil-scheme-morphism-properties] $K_0$-schemes, and let $f:X\to Y$ be a
separated finite-type $K_0$-morphism. Fix a prime $\ell$, write
$\Ql=\mathbf Q_\ell$, and require that its image in $K_0$ is invertible.
Choose a finite extension $E/\Ql$, an integer $n\in\mathbf Z_{\geq1}$, and
put $A=A_{E,n}$. Let $c=(j,\bar f)$ be an object of the compactification
category [def-weil-compactifications-refinements] $\operatorname{Comp}(f)$.
Using the finite-torsion coefficient sheaves
[def-weil-finite-torsion-constructibility] $A$, the derived direct image
[def-weil-derived-direct-image] $R\bar f_{*,n}$, and the extension-by-zero
functor [def-weil-extension-by-zero] $j_!$, set

$$
 Rf_{!,n}^{c}=R\bar f_{*,n}\,j_!:
 D(X_{\mathrm{proet}},A)
 \longrightarrow D(Y_{\mathrm{proet}},A),
$$

a functor attached to the chosen compactification $c$. Every property
asserted of it in this blueprint — independence of the chosen
compactification, base-change compatibility, coherence and the finite-level
comparisons — is asserted on the full subcategory $\mathcal
D^{+}_{\mathrm{et}}(X,A)\subseteq D(X_{\mathrm{proet}},A)$ of complexes that
*come from the etale site* in the sense of the etale-origin witness of the
proper-base-change chapter, a forward reference since the comparison morphism
of sites is introduced there; that subcategory contains the finite-torsion
constructible complexes of [def-weil-finite-torsion-constructibility]
together with their witnesses. On $\mathcal D^{+}_{\mathrm{et}}(X,A)$ the
functor is independent of $c$, so there the superscript may be dropped; off
that subcategory nothing beyond the displayed formula is asserted, and in
particular no independence, base-change or constructibility claim is made.
Here $R\bar f_{*,n}$ is computed by a K-injective resolution and $j_!$ is
exact.
