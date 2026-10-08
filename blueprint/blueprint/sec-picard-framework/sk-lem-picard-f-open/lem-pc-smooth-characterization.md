+++
id = "lem-pc-smooth-characterization"
kind = "lemma"
title = "Smoothness versus flatness"
order = 822
uses = ["def-pc-base-change", "def-pc-morphism-conventions", "def-weil-scheme-morphism-properties"]
+++
Let $f:X\to S$ be a morphism of
locally finite presentation.
Then $f$ is smooth if and only if $f$
is flat and every fibre $X_s$ is smooth over $\kappa(s)$.

## Proof

($\Leftarrow$) This is Morphisms of Schemes, Lemma 29.35.3 (Tag
[01V8](https://stacks.math.columbia.edu/tag/01V8)) (the proof of
which is the local algebra criterion Algebra, Lemma 10.137.16, Tag
[00TF](https://stacks.math.columbia.edu/tag/00TF): after inverting
one element, the ring map is a relative global complete intersection
whose Jacobian is invertible, which is the definition of a standard
smooth ring map).

($\Rightarrow$) We may work Zariski-locally and assume $S=\operatorname{Spec}(R)$ and
$X=\operatorname{Spec}(A)$ with $R\to A$ smooth at a prime $\mathfrak q$; assume
$A$ is standard smooth over $R$, i.e. $A=R[x_1,\dots,x_n]/(f_1,\dots,f_c)$ with the Jacobian
$\det(\partial f_j/\partial x_i)_{i,j\le c}$ a unit in $A$ (Algebra,
Lemma 10.137.6, Tag [00T7](https://stacks.math.columbia.edu/tag/00T7),
which also gives the Zariski-locality: smooth ring maps are
Zariski-locally standard smooth). *Finite presentation* holds by
definition. *Flatness:* the elements $f_1,\dots,f_c$ form a
regular sequence of $R[x]$: after the invertible linear change of
variables $x_i\mapsto x_i-a_i$ we may assume the Jacobian is invertible
at $\mathfrak q$, so the initial forms of the $f_j$ in the graded ring
are $x_1,\dots,x_c$, and a sequence whose initial forms in a regular
sequence, is regular; hence the Koszul complex
$0\to\wedge^cR[x]^c\to\cdots\to R[x]^c\to R[x]\to A\to0$ is exact
(exactness of the Koszul complex of a regular sequence), a projective
(hence flat) resolution of $A$; $A$ is flat over $R$.
*Smooth fibres:* for $\mathfrak p\subset R$ the base change
$A\otimes_R\kappa(\mathfrak p)$ is standard smooth over
$\kappa(\mathfrak p)$ (Algebra, Lemma 10.137.3, Tag
[00T4](https://stacks.math.columbia.edu/tag/00T4)), hence smooth
(Lemma 10.137.6, Tag 00T7). The general statement follows by
Zariski-locality.
