+++
id = "lemma-weil-pbc-composition"
kind = "lemma"
title = "Composition of proper maps"
order = 1194
uses = ["lemma-weil-pbc-proper-underived-exchange", "lemma-weil-pbc-property-iff-acyclicity"]
+++
Suppose $X\xrightarrow{f}Y\xrightarrow{h}Z$ are proper and both satisfy
$\mathsf{IA}$. Then $hf$ satisfies $\mathsf{IA}$ and hence $\mathsf{PBC}$.

## Proof

Let $a:Z'\to Z$ be a base change, $Y'=Y\times_ZZ'$, $X'=X\times_Y Y'$, and
$I$ an injective $\mathbf F_\ell$-module sheaf on $X$. Since inverse image is exact, $f_*$ (a right adjoint)
sends injectives to injectives: for an epimorphism $A\twoheadrightarrow B$,
the map $\operatorname{Hom}(B,f_*I)\to\operatorname{Hom}(A,f_*I)$ identifies
with $\operatorname{Hom}(f^{-1}B,I)\to\operatorname{Hom}(f^{-1}A,I)$ and is
surjective. The proper underived exchange lemma identifies
$f'_*a_X^{-1}I\cong b^{-1}f_*I$, where $b:Y'\to Y$ is the base change.
The Grothendieck spectral sequence has terms

$$
E_2^{p,q}=R^ph'_*\,R^qf'_*\,a_X^{-1}I
\Longrightarrow R^{p+q}(h'f')_*a_X^{-1}I,
$$

where $a_X:X'\to X$ and $h':Y'\to Z'$ are the base changes. The
first-quadrant hypotheses are: this sheaf is $h'_*$-acyclic by the assumed
$\mathsf{IA}(h)$, and $a_X^{-1}I$ is
$f'_*$-acyclic by $\mathsf{IA}(f)$. Thus the $q>0$ rows vanish, then the
$p>0$ column of the surviving row vanishes, so all terms with $p+q>0$
vanish. The spectral sequence converges because each total degree has only
finitely many pairs $(p,q)$. This is the calculation located at Tag
`0A4D`.
