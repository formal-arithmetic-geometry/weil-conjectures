+++
id = "def-weil-ambient-exceptional-adjoint"
kind = "definition"
title = "Ambient exceptional right adjoint datum"
order = 1488
uses = ["def-compact-support-direct-image-detailed", "def-weil-compactifications-refinements", "def-weil-exceptional-adjoint-admissibility", "def-weil-full-cohomological-dimension", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and put $A=A_{E,n}$. Let $S$ be a scheme on which $\ell$ is
invertible, let $X,Y$ be finite-type
[def-weil-scheme-morphism-properties] $S$-schemes, and let $f:X\to Y$ be a
separated finite-type $S$-morphism, with a compactification
[def-weil-compactifications-refinements] $X\xrightarrow{j}\overline
X\xrightarrow{p}Y$. Say that $f$ carries the *ambient exceptional right
adjoint datum at $A$* if clause (1) of
[def-weil-exceptional-adjoint-admissibility] holds: the full
cohomological-dimension condition [def-weil-full-cohomological-dimension]
$\operatorname{FullCD}(p,A;c_{\mathrm{cd}})$ holds for some
$c_{\mathrm{cd}}\in\mathbf Z_{\geq0}$, the compact-support direct image
[def-compact-support-direct-image-detailed] $Rf_{!,n}$ has a right adjoint
$Rf_n^{\times}$ on the *ordinary* derived categories of the small pro-etale
sites [def-weil-pbc-proetale-site],

$$
 \operatorname{Hom}_Y\bigl(Rf_{!,n}K,L\bigr)\cong
 \operatorname{Hom}_X\bigl(K,Rf_n^{\times}L\bigr),
$$

and for every refinement of the compactification the units, counits and
comparison maps agree. This datum asserts the *existence* of the ambient
right adjoint and nothing about its values; it says nothing about
constructibility or finite Tor amplitude.

*Warning.* This datum is not satisfied in general. Its $\operatorname{FullCD}$ clause quantifies over *every* pro-etale sheaf of $A$-modules, and that fails already for the structure morphism of an elliptic curve $E$ over $\overline{\mathbf F}_p$ with $A=\mathbf F_r$, $r\neq p$: there is a pro-etale $A$-module sheaf $\mathcal F$ on $E$, not of etale origin, with $H^n(E_{\mathrm{proet}},\mathcal F)\neq0$ for every $n\geq1$, so $Rf_*=Rf_!$ does not preserve the coproduct $\bigoplus_n\mathcal F[n]$ and has no right adjoint on $D(E_{\mathrm{proet}},A)$ nor on $D^+$ (rem:sf-ambient-counterexample in the six-functors chapter). The datum is therefore never assumed on the proof chain of this blueprint; what is used is the constructible exceptional adjoint of def-weil-exceptional-inverse-image, whose existence and adjunction on the bounded-below complexes of etale origin is the theorem thm-sf-ambient-adjoint-class and whose preservation clauses are thm-sf-preservation-class.
