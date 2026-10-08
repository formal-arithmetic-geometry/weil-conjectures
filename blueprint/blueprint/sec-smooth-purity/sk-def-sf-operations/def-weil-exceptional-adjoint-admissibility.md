+++
id = "def-weil-exceptional-adjoint-admissibility"
kind = "definition"
title = "Exceptional-adjoint admissibility"
order = 1474
uses = ["def-weil-compactifications-refinements", "def-weil-constructible-intervals", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-full-cohomological-dimension", "def-weil-scheme-morphism-properties"]
+++
Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and put $A=A_{E,n}$. Let $S$ be a scheme on which $\ell$ is
invertible, let $X,Y$ be finite-type
[def-weil-scheme-morphism-properties] $S$-schemes, and let $f:X\to Y$ be a
separated finite-type $S$-morphism. Choose a compactification
[def-weil-compactifications-refinements] $X\xrightarrow{j}\overline
X\xrightarrow{p}Y$, so $j$ is an open immersion and $p$ is proper. Use
finite-torsion constructibility
[def-weil-finite-torsion-constructibility]. Say that $f$ is
*exceptional-adjoint admissible at $A$* if:

1. the full cohomological-dimension condition
   [def-weil-full-cohomological-dimension]
   $\operatorname{FullCD}(p,A;c_{\mathrm{cd}})$ holds for some
   $c_{\mathrm{cd}}\in\mathbf Z_{\geq0}$, and $Rf_n^{\times}$ is a right
   adjoint to $Rf_{!,n}$ on the ambient derived categories, and for every
   refinement its units, counits, and comparison maps agree;
2. there are *signed* integers $c_f^-,c_f^+\in\mathbf Z$ such that, for every
   pair of integers $a\leq b$, with $D_c^{[a,b]}$ the constructible
   cohomological interval subcategory
   [def-weil-constructible-intervals],
   $$
    L\in D_c^{[a,b]}(Y,A)\Longrightarrow
    Rf_n^{\times}L\in D_c^{[a+c_f^-,b+c_f^+]}(X,A);
   $$
   the constants record the cohomological bounds of the right adjoint. Their
   signs allow shifts in either direction; proving these bounds for a
   particular geometric morphism is a separate obligation.
3. for the finite-Tor subcategory [def-weil-finite-tor-amplitude]
   $D^b_{ctf}(Y,A)$, one has
   $$
    L\in D^b_{ctf}(Y,A)
   \Longrightarrow
    Rf_n^{\times}L\in D^b_{ctf}(X,A).
   $$

For $\Lambda\in\{\mathcal O_E,E,\Qlb\}$, call $f$ admissible at $\Lambda$
when the three displayed conditions hold at every finite coefficient stage
with uniform bounds and when the finite-reduction and scalar-extension maps
for the corresponding right adjoints are isomorphisms. These are proof
obligations for restriction of an ambient right adjoint, not consequences of
the definition of a separated finite-type morphism.

*Warning.* Clause (1) is not satisfied in general: its
$\operatorname{FullCD}$ condition fails for the structure morphism of an
elliptic curve over $\overline{\mathbf F}_p$ with $A=\mathbf F_r$, $r\neq p$,
and for that morphism $Rf_!=Rf_*$ has no right adjoint on the ambient derived
category, nor on $D^+$ (rem:sf-ambient-counterexample in the six-functors
chapter). Hence the structure morphism of a smooth proper variety may *not*
be presupposed exceptional-adjoint admissible in this sense, and no statement
on the proof chain of this blueprint assumes it. What the blueprint uses is
the constructible exceptional adjoint of def-weil-exceptional-inverse-image,
defined without clause (1) from the etale adjoint; for it the analogues of
(1)–(3) on $D^b_c$ and $D^b_{ctf}$ are theorems for every separated
finite-type morphism of finite-type $k$-schemes (thm-sf-ambient-adjoint-class
for the adjunction, thm-sf-preservation-class for the two preservation
clauses with the constants $c_f^-=-2D$, $c_f^+=2\dim Y+1$). The present
definition is retained only to name the stronger, optional, ambient notion.
