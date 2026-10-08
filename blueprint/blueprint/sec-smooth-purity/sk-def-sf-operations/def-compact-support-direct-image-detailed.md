+++
id = "def-compact-support-direct-image-detailed"
kind = "definition"
title = "Compactification-independent finite-level direct image"
order = 1486
uses = ["def-weil-compact-support-candidate", "def-weil-compactifications-refinements", "def-weil-finite-torsion-constructibility", "def-weil-pbc-etale-origin-witness", "def-weil-scheme-morphism-properties", "prop-compactification-coherence-detailed"]
+++
Let $K_0$ be a field, let $X,Y$ be finite-type
[def-weil-scheme-morphism-properties] $K_0$-schemes, and let $f:X\to Y$ be a
separated finite-type $K_0$-morphism. Fix a prime $\ell$, write
$\Ql=\mathbf Q_\ell$, and require that its image in $K_0$ is invertible.
Choose a finite extension $E/\Ql$, an integer $n\in\mathbf Z_{\geq1}$, and
put $A=A_{E,n}$. Use finite-torsion coefficients
[def-weil-finite-torsion-constructibility] and the compact-support candidate
[def-weil-compact-support-candidate]. Choose an object
$c\in\operatorname{Comp}(f)$ in the compactification category
[def-weil-compactifications-refinements] and define

$$
 Rf_{!,n}=Rf_{!,n}^{c}:
 D(X_{\mathrm{proet}},A_{E,n})
 \longrightarrow D(Y_{\mathrm{proet}},A_{E,n}),
$$

the functor of [def-weil-compact-support-candidate] attached to $c$. Its
independence of the chosen compactification, and every other property
asserted of it in this blueprint, are asserted on the subcategory $\mathcal
D^{+}_{\mathrm{et}}(X,A_{E,n})$ of that definition, namely on the complexes
that come from the etale site with an etale-origin witness; there the
superscript is dropped. For a refinement $u:c_1\to c_2$, use the natural
comparison isomorphism $Rf_{!,n}^{c_1}\xrightarrow{\sim}Rf_{!,n}^{c_2}$
induced by proper composition and extension by zero. Require these
comparisons to be the identity for identity refinements and transitive under
composition. The independence of the resulting functor from the chosen object
$c$, and the cocycle condition for the comparisons through a common
refinement, are the compactification-coherence proposition; that $Rf_{!,n}$
is a triangulated functor is
[lem-compact-support-direct-image-triangulated].
